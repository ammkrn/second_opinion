use std::fmt::Debug;
use std::path::PathBuf;
use std::fs::OpenOptions;
use std::io::Read;
use mm0b_parser::BasicMmbFile;
use mm0_util::{ SortId, Modifiers };
use crate::util::Res;
use crate::util::VerifErr;
use crate::conv_err;
use crate::none_err;
use crate::io_err;


#[derive(Debug, PartialEq, Eq)]
pub enum ImportGraph {
    NoImports(PathBuf),
    HasImports(PathBuf, Vec<ImportGraph>),
}

pub struct RawFileData {
    mmb_bytes: Vec<u8>,
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
    mmz_strings: Vec<String>,
    // The structure of the import hierarchy. Might be useful to let users
    // inspect/view this as part of the output.
    #[allow(dead_code)]
    pub(crate) mmz_hierarchy: ImportGraph,
}

#[derive(Debug)]
pub struct FileView<'a> {
    pub mmb: BasicMmbFile<'a>,
    pub mmz: &'a [String]
}

impl<'a> FileView<'a> {
    pub(crate) fn mmb_sort_mods(&self, id: SortId) -> Res<Modifiers> {
        use std::convert::TryFrom;
        none_err!(self.mmb.sort(id))
        .and_then(|id| conv_err!(Modifiers::try_from(id)))
    }
}

pub struct MmzImporter {
    root_mmz_path: PathBuf,
    mmz_strings: Vec<String>,
    /// For detecting cycles
    todos: Vec<PathBuf>,
    /// For detecting diamonds
    done: Vec<PathBuf>,
}

impl MmzImporter {
    pub fn new_from(root_mmz_path: PathBuf) -> Self {
        MmzImporter {
            root_mmz_path,
            mmz_strings: Vec::new(),
            todos: Vec::new(),
            done: Vec::new()
        }
    }

    pub fn w_filename(&self, filename: impl AsRef<std::ffi::OsStr>) -> PathBuf {
        let mut new_path = self.root_mmz_path.clone();
        new_path.set_file_name(filename);
        new_path
    }

    /// Form the import graph by mutual recursion with `add_mmz_aux`.
    /// Open the specified file, look for any import statements therein. If there are any,
    /// Do the same thing with those.
    fn add_mmz(
        &mut self,
        mmz_path: impl Into<PathBuf>,
    ) -> Res<ImportGraph> {
        let mmz_path = mmz_path.into();
        self.todos.push(mmz_path.clone());
        // Read the current file so we can find the import statements, but don't
        // push it to the list of mmz files yet so that we maintain the
        // primtive >> uses imports
        // directional ordering.
        let s = io_err!(std::fs::read_to_string(&mmz_path))?;

        // Find any imports in `s` and add them (and their imports) to the accumulator
        let imports = self.add_mmz_aux(s.split_whitespace())?;
        // NOW we can push it.
        self.mmz_strings.push(s);
        // Take this file off the stack of `todos` now that we've collected its imports
        let popped = none_err!(self.todos.pop())?;
        debug_assert_eq!(popped, mmz_path);
        // push the path onto `done` so we can detect cycles.
        self.done.push(popped);
        if imports.is_empty() {
            Ok(ImportGraph::NoImports(mmz_path))
        } else {
            Ok(ImportGraph::HasImports(mmz_path, imports))
        }
    }

    /// Form the import graph by mutual recursion with `add_mmz`.
    fn add_mmz_aux(
        &mut self, 
        mut ws: std::str::SplitWhitespace,
    ) -> Res<Vec<ImportGraph>> {
        let mut acc = Vec::<ImportGraph>::new();
        while let Some(fst) = ws.next() {
            // If there's a chunk starting with the `import` keyword
            if fst == "import" {
                match ws.next() {
                    Some(path) if path.starts_with("\"") && path.ends_with("\";") => {
                        // Get the path without the quotes and semicolon
                        let pathbuf = PathBuf::from(&path[1..path.len() - 2]);
                        // This is part of a diamond that's already been added, so just skip this loop iteration.
                        if self.done.iter().any(|done| done == &self.w_filename(&pathbuf)) {
                            continue
                        } else if self.todos.iter().any(|todo| todo == &self.w_filename(&pathbuf)) {
                            return Err(VerifErr::Msg(format!("Import cycle detected")))
                        }
                        let hierarchy = self.add_mmz(self.w_filename(pathbuf))?;
                        acc.push(hierarchy);
                    },
                    _ => continue
                }
            }
        }
        Ok(acc)
    }    
}

impl RawFileData {
    pub fn view<'a>(&'a self) -> Res<FileView<'a>> {
        mm0b_parser::BasicMmbFile::parse(self.mmb_bytes.as_slice())
            .map_err(|e| VerifErr::Msg(format!("{:?}", e)))
            .map(|mmb|
                FileView {
                    mmb,
                    mmz: self.mmz_strings.as_slice()
                }
            )
    }

    pub fn new_from(mmb_path: impl Into<PathBuf>, root_mmz_path: Option<impl Into<PathBuf>>) -> Res<Self> {
    
        let mmb_path = io_err!(mmb_path.into().canonicalize())?;
        // If there was no mmz_path specified, look for an mm0 file
        // in the same location as the mmb file.
        let root_mmz_path = match root_mmz_path {
            None => {
                let mut base = mmb_path.clone();
                base.set_extension("mm0");
                base
            },
            Some(p) => io_err!(p.into().canonicalize())?
        };
        
        let mut mmb_handle = io_err! {
            OpenOptions::new()
            .read(true)
            .truncate(false)
            .open(&mmb_path)
        }?;

        let mut mmb_bytes = Vec::<u8>::with_capacity(io_err!(mmb_handle.metadata())?.len() as usize);
        io_err!(mmb_handle.read_to_end(&mut mmb_bytes))?;

        let mut mmz_import_garbage = MmzImporter::new_from(root_mmz_path.clone());
        let mmz_hierarchy = mmz_import_garbage.add_mmz(root_mmz_path)?;
        let data = RawFileData {
            mmb_bytes,
            mmz_strings: mmz_import_garbage.mmz_strings,
            mmz_hierarchy,
        };
        Ok(data)        
    }
}


#[test]
fn import_test1() {

    let file_data1 = RawFileData::new_from("./test_resources/a.mmb",  Some("./test_resources/a.mm0")).unwrap();
    let file_data2 = RawFileData::new_from("./test_resources/a.mmb", None::<String>).unwrap();
    assert_eq!(file_data1.mmz_hierarchy, file_data2.mmz_hierarchy);
    let d = ImportGraph::NoImports(PathBuf::from("./test_resources/d.mm0").canonicalize().unwrap());
    let e = ImportGraph::NoImports(PathBuf::from("./test_resources/e.mm0").canonicalize().unwrap());
    let f = ImportGraph::NoImports(PathBuf::from("./test_resources/f.mm0").canonicalize().unwrap());
    let g = ImportGraph::NoImports(PathBuf::from("./test_resources/g.mm0").canonicalize().unwrap());
    let b = ImportGraph::HasImports(PathBuf::from("./test_resources/b.mm0").canonicalize().unwrap(), vec![d, e]);
    let c = ImportGraph::HasImports(PathBuf::from("./test_resources/c.mm0").canonicalize().unwrap(), vec![f, g]);
    let a = ImportGraph::HasImports(PathBuf::from("./test_resources/a.mm0").canonicalize().unwrap(), vec![b, c]);
    assert_eq!(file_data1.mmz_hierarchy, a);
}

#[test]
fn import_test_diamond1() {
    let file_data= RawFileData::new_from("./test_resources/diamond/a.mmb", Some("./test_resources/diamond/a.mm0")).unwrap();
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
    let _ = RawFileData::new_from("./test_resources/cycle/cycle.mmb", Some("./test_resources/cycle/cycleA.mm0")).unwrap();
}
