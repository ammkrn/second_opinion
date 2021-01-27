#![forbid(unsafe_code)]
#![forbid(unreachable_patterns)]
#![forbid(unused_mut)]
#![forbid(unused_variables)]
#![forbid(unused_must_use)]
#![forbid(unused_imports)]

#![allow(unused_parens)]
// Temporary.
#![allow(dead_code)]

mod util;
mod mmb;
mod mmz;
mod formatting;
mod fs;

use std::path::PathBuf;
use clap::{ Arg, App };
use crossbeam_utils::thread;
use std::sync::atomic::{ AtomicUsize, Ordering::Relaxed };
use crate::mmb::MmbMem;
use crate::mmz::MmzMem;
use crate::util::VerifErr;
use crate::fs::FileData;
use crate::util::Outline;

fn main() {
    let start = std::time::Instant::now();
    let matches = App::new("Verifier")
        .version("0.1")
        .author("ammkrn@tuta.io")
        .about("A metamath zero verifier")
        .arg(
            Arg::with_name("num_threads")
            .short("t")
            .long("threads")
            .help("specify the number of threads to use")
            .takes_value(true)
        )
        .arg(
            Arg::with_name("mmb_file")
            .value_name("mmb file")
            .required(true)
            .takes_value(true)
        )
        .arg(
            Arg::with_name("mmz_file")
            .value_name("mmz file")
            .required(false)
            .takes_value(true)
        )
        .get_matches();
                            

    let num_threads = match matches.value_of("num_threads") {
        None => 1,
        Some(s) => match s.parse::<usize>() {
            Ok(0) => 1,
            Ok(n) => n,
            Err(_) => {
                panic!()
            }
        }
    };

    // Safe to unwrap since this is required by the clap app.
    let mmb_path = matches.value_of("mmb_file").map(|s| PathBuf::from(s)).unwrap();
    let mmz_path = matches.value_of("mmz_file").map(|s| PathBuf::from(s));


    let file_data = FileData::new_from(mmb_path, mmz_path).unwrap();
    let outline = Outline::new_from(&file_data).unwrap();

    // Now that all the file IO is done, we can confidently begin verification.
    let summary = if num_threads == 1 {
        verify_serial(&outline)
    } else {
        verify_par(&outline, num_threads)
    };

    if let Some((e, es)) = summary.errs.split_first() {
        println!("verification was unsuccessful. Terminated with error {:?}\n + {} other errors", e, es.len());
    } else {
        // These are "hard" assertions since the absence of errors in `summary.errs` should indicate
        // that these are equal. If they're not, there's been a logic error somewhere.
        // Also, we can unwrap mmz_mem since it has to be `Some` at this point.
        assert_eq!(outline.header.num_sorts, outline.mmb_num_sorts_done());
        assert_eq!(outline.header.num_terms, outline.mmb_num_termdefs_done());
        assert_eq!(outline.header.num_thms, outline.mmb_num_asserts_done());

        assert_eq!(outline.header.num_sorts, summary.mmz_mem.as_ref().unwrap().num_sorts_done());
        assert_eq!(outline.header.num_terms, summary.mmz_mem.as_ref().unwrap().num_termdefs_done());
        assert_eq!(outline.header.num_thms, summary.mmz_mem.as_ref().unwrap().num_asserts_done());
        println!(
            "\n* verified {} sorts, {} terms, and {} assertions in {}ms", 
            outline.header.num_sorts, 
            outline.header.num_terms, 
            outline.header.num_thms, 
            start.elapsed().as_millis()
        );
    }
}

fn verify_serial<'a>(outline: &'a Outline<'a>) -> VerifResults<'a> {
    let task_counter = AtomicUsize::new(0);
    let (mmz_mem, mut errs) = verify_mmz(outline);
    let (mmb_mem, mut mmb_errs) = verify_mmb(outline, &task_counter);
    errs.append(&mut mmb_errs);

    VerifResults {
        mmz_mem: Some(mmz_mem),
        mmb_mems: vec![mmb_mem],
        errs
    }
}

struct VerifResults<'a> {
    mmz_mem: Option<MmzMem<'a>>,
    mmb_mems: Vec<MmbMem<'a>>,
    errs: Vec<VerifErr>,
}

fn verify_par<'a>(outline: &'a Outline<'a>, num_threads: usize) -> VerifResults<'a> {
    let task_counter = AtomicUsize::new(0);

    thread::scope(|sco| {
        let mut mmb_tasks = Vec::new();

        for _ in 0..num_threads {
            mmb_tasks.push(sco.spawn(|_| verify_mmb(outline, &task_counter)));
        }

        let (mmz_mem, mut errs) = match sco.spawn(|_| verify_mmz(outline)).join() {
            Err(_) => (None, vec![VerifErr::Msg(format!("mmz thread panicked!"))]),
            Ok((mem, errs)) => (Some(mem), errs),
        };

        let mut mmb_mems = Vec::new();
        for (idx, mmb_task) in mmb_tasks.into_iter().enumerate() {
            match mmb_task.join() {
                Err(_) => { errs.push(VerifErr::Msg(format!("mmb thread {} panicked", idx))); },
                Ok((mem, mut mmb_errs)) => {
                    errs.append(&mut mmb_errs);
                    mmb_mems.push(mem);
                }
            }
        }

        VerifResults { mmz_mem, mmb_mems, errs }
    }).unwrap()
}

// Parsing/verifying the contents of the mmz file is done in serial
fn verify_mmz<'a>(outline: &'a Outline<'a>) -> (MmzMem<'a>, Vec<VerifErr>) {
    let mut mem = MmzMem::new_from(outline).unwrap();
    let mut errs = Vec::new();
    for (stmt, _proof) in outline.declarations.iter() {
        if let Err(e) = mem.verify1(*stmt) {
            errs.push(e);
        }
    }

    (mem, errs)
}

fn verify_mmb<'a>(outline: &'a Outline<'a>, task_counter: &AtomicUsize) -> (MmbMem<'a>, Vec<VerifErr>) {
    let mut mmb_mem = MmbMem::new_from(outline).unwrap();
    let mut errs = Vec::new();
    while let Some((stmt, proof)) = outline.declarations.get(task_counter.fetch_add(1, Relaxed)) {
        if let Err(e) = mmb_mem.verify1(*stmt, *proof) {
            errs.push(e);
        }
    }
    (mmb_mem, errs)
}
