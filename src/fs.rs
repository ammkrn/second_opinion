use std::path::PathBuf;
use crate::util::Res;
use crate::util::VerifErr;

use std::fmt::{ Debug, Formatter, Result as FmtResult };


#[derive(Debug, PartialEq, Eq)]
pub enum ImportGraph {
    NoImports(PathBuf),
    HasImports(PathBuf, Vec<ImportGraph>),
}

pub struct FileData {
    pub mmb_file: Vec<u8>,
    /// From left to right, represents a backwards depth-first walk
    /// of the dependency graph, so if we have:
    ///```text
    ///      a
    ///     /  \
    ///    b   c
    ///  / \   / \
    /// d  e  f   g
    ///```
    /// then the vec contains [d, e, b, f, g, c, a]
    pub mmz_files: Vec<String>,
    // The structure of the import hierarchy. Might be useful to let users
    // inspect/view this as part of the output.
    pub mmz_hierarchy: ImportGraph,
    root_mmz_path: PathBuf,
    // For detecting cycles
    todos: Vec<PathBuf>,
    // For detecting diamonds
    done: Vec<PathBuf>,
}

impl std::default::Default for FileData {
    fn default() -> Self {
        FileData {
            mmb_file: Vec::new(),
            mmz_files: Vec::new(),
            root_mmz_path: PathBuf::from(""),
            mmz_hierarchy: ImportGraph::NoImports(PathBuf::from("")),
            todos: Vec::new(),
            done: Vec::new(),
        }
    }
}

use std::fs::OpenOptions;
use std::io::Read;
impl FileData {
    pub fn w_filename(&self, filename: impl AsRef<std::ffi::OsStr>) -> PathBuf {
        let mut new_path = self.root_mmz_path.clone();
        new_path.set_file_name(filename);
        new_path
    }

    pub fn new_from(mmb_path: impl Into<PathBuf>,  root_mmz_path: Option<impl Into<PathBuf>>) -> Res<Self> {
        let mmb_path = mmb_path.into().canonicalize().unwrap();
        let root_mmz_path = match root_mmz_path {
            None => {
                let mut base = mmb_path.clone();
                base.set_extension("mm0");
                base
            },
            Some(p) => p.into().canonicalize().unwrap()
        };
        
        let mut mmb_handle = OpenOptions::new()
            .read(true)
            .truncate(false)
            .open(&mmb_path)
            .map_err(|_| VerifErr::Msg(format!("IO err in add_file mmb")))
            .unwrap();    

        let mut mmb_file = Vec::<u8>::with_capacity(mmb_handle.metadata().unwrap().len() as usize);
        mmb_handle.read_to_end(&mut mmb_file).unwrap();        

        let mut data = FileData::default();
        data.mmb_file = mmb_file;
        data.root_mmz_path = root_mmz_path.clone();
        data.mmz_hierarchy = data.add_mmz_aux(root_mmz_path)?;
        Ok(data)        
    }

    /// Form the import graph by mutual recursion with `find_imports`.
    /// Open the specified file, look for any import statements therein. If there are any,
    /// Do the same thing with those.
    fn add_mmz_aux(&mut self, mmz_path: impl Into<PathBuf>) -> Res<ImportGraph> {
        let mmz_path = mmz_path.into();
        self.todos.push(mmz_path.clone());
        let s = std::fs::read_to_string(&mmz_path).unwrap();

        let imports = self.find_imports(s.split_whitespace())?;
        self.mmz_files.push(s);
        let popped = self.todos.pop().unwrap();
        debug_assert_eq!(popped, mmz_path);
        self.done.push(popped);
        if imports.is_empty() {
            Ok(ImportGraph::NoImports(mmz_path))
        } else {
            Ok(ImportGraph::HasImports(mmz_path, imports))
        }
    }

    /// Form the import graph by mutual recursion with `add_mmz_aux`.
    fn find_imports(&mut self, mut ws: std::str::SplitWhitespace) -> Res<Vec<ImportGraph>> {
        let mut acc = Vec::<ImportGraph>::new();
        while let Some(fst) = ws.next() {
            if fst == "import" {
                match ws.next() {
                    Some(path) if path.starts_with("\"") => {
                        let end_pos = path.chars().skip(1).position(|c| c == '"').unwrap();
                        let pathbuf = PathBuf::from(&path[1..end_pos + 1]);
                        // This is part of a diamond that's already been added, so just skip this loop iteration.
                        if self.done.iter().any(|done| done == &self.w_filename(&pathbuf)) {
                            continue
                        } else if self.todos.iter().any(|todo| todo == &self.w_filename(&pathbuf)) {
                            return Err(VerifErr::Msg(format!("Import cycle detected")))
                        }
                        let hierarchy = self.add_mmz_aux(self.w_filename(pathbuf))?;
                        acc.push(hierarchy);
                    },
                    _ => continue
                }
            }
        }
        Ok(acc)
    }
}


impl Debug for FileData {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        let mut d = f.debug_struct("FileData");
        d.field("mmz_files", &"<omitted>");
        d.field("mmz_hierarchy", &self.mmz_hierarchy);
        d.field("todos", &self.todos);
        d.field("done", &self.done);
        d.field("root_mmz_file", &self.root_mmz_path);
        d.finish()
    }
}


#[test]
fn import_test1() {

    let file_data = FileData::new_from("./test_resources/a.mmb", Some("./test_resources/a.mm0")).unwrap();
    let file_data2 = FileData::new_from("./test_resources/a.mmb", None::<String>).unwrap();
    assert_eq!(file_data.mmz_hierarchy, file_data2.mmz_hierarchy);
    let d = ImportGraph::NoImports(PathBuf::from("./test_resources/d.mm0").canonicalize().unwrap());
    let e = ImportGraph::NoImports(PathBuf::from("./test_resources/e.mm0").canonicalize().unwrap());
    let f = ImportGraph::NoImports(PathBuf::from("./test_resources/f.mm0").canonicalize().unwrap());
    let g = ImportGraph::NoImports(PathBuf::from("./test_resources/g.mm0").canonicalize().unwrap());
    let b = ImportGraph::HasImports(PathBuf::from("./test_resources/b.mm0").canonicalize().unwrap(), vec![d, e]);
    let c = ImportGraph::HasImports(PathBuf::from("./test_resources/c.mm0").canonicalize().unwrap(), vec![f, g]);
    let a = ImportGraph::HasImports(PathBuf::from("./test_resources/a.mm0").canonicalize().unwrap(), vec![b, c]);
    assert_eq!(file_data.mmz_hierarchy, a);
}

#[test]
fn import_test_diamond1() {
    let file_data= FileData::new_from("./test_resources/diamond/a.mmb", Some("./test_resources/diamond/a.mm0")).unwrap();
    let d = ImportGraph::NoImports(PathBuf::from("test_resources/diamond/d.mm0").canonicalize().unwrap());
    let e = ImportGraph::NoImports(PathBuf::from("test_resources/diamond/e.mm0").canonicalize().unwrap());
    let f = ImportGraph::NoImports(PathBuf::from("test_resources/diamond/f.mm0").canonicalize().unwrap());
    let g = ImportGraph::NoImports(PathBuf::from("test_resources/diamond/g.mm0").canonicalize().unwrap());
    let b = ImportGraph::HasImports(PathBuf::from("test_resources/diamond/b.mm0").canonicalize().unwrap(), vec![d, e]);
    let c = ImportGraph::HasImports(PathBuf::from("test_resources/diamond/c.mm0").canonicalize().unwrap(), vec![f, g]);
    let a = ImportGraph::HasImports(PathBuf::from("test_resources/diamond/a.mm0").canonicalize().unwrap(), vec![b, c]);
    assert_eq!(file_data.mmz_hierarchy, a);
}

#[test]
#[should_panic]
fn import_test_cycle1() {
    let _ = FileData::new_from("./test_resources/cycle/cycle.mmb", Some("./test_resources/cycle/cycleA.mm0")).unwrap();
}
