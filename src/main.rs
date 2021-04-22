#![forbid(unsafe_code)]
#![forbid(unreachable_patterns)]
#![forbid(unused_mut)]
#![forbid(unused_variables)]
#![forbid(unused_must_use)]
#![forbid(unused_imports)]
#![allow(unused_parens)]

mod util;
mod mmb;
mod mmz;
mod fs;

use std::path::PathBuf;
use std::sync::atomic::{ AtomicUsize, Ordering::Relaxed };
use bumpalo::Bump;
use clap::{ Arg, App };
use crossbeam_utils::thread;
use crate::mmz::MmzMem;
use crate::fs::{ RawFileData };
use crate::util::{ Res, Outline, VerifErr };

fn main() {
    let start = std::time::Instant::now();
    let matches = App::new("Verifier")
        .version("0.2")
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
            Err(_) => panic!("The number of threads must be a natural number. got {}", s)
        }
    };

    // Safe to unwrap since this is required by the clap app.
    let mmb_path = matches.value_of("mmb_file").map(|s| PathBuf::from(s)).unwrap();
    let mmz_path = matches.value_of("mmz_file").map(|s| PathBuf::from(s));

    let raw_file = match RawFileData::new_from(mmb_path, mmz_path) {
        Ok(data) => data,
        Err(e) => {
            eprintln!("Failed to obtain file data: {:?}\n", e);
            panic!()
        }
    };
    let file_view = match raw_file.view() {
        Ok(v) => v,
        Err(e) => {
            eprintln!("mm0-rs mm0b_parser failed to parse mmb file: {:?}\n", e);
            panic!()
        }
    };

    let outline = match Outline::new_from(&file_view) {
        Ok(ol) => ol,
        Err(e) => {
            eprintln!("failed to create verification outline: {:?}\n", e);
            panic!()
        }
    };

    // Now that all the file IO is done, we can confidently begin verification.
    let verif_result = if num_threads == 1 {
        verify_serial(&outline)
    } else {
        verify_par(&outline, num_threads)
    };

    if let Err(e) = verif_result {
        eprintln!("verification was unsuccessful. Terminated with error {:?}\n", e)
    } else {
        println!(
            "\n* verified {} sorts, {} terms, and {} assertions in {}ms", 
            outline.file_view.mmb.header.num_sorts, 
            outline.file_view.mmb.header.num_terms, 
            outline.file_view.mmb.header.num_thms, 
            start.elapsed().as_millis()
        );
    }
}

fn verify_serial<'a>(outline: &'a Outline<'a>) -> Res<()> {
    let task_counter = AtomicUsize::new(0);
    verify_mmz(outline)?;
    verify_mmb(outline, &task_counter)?;
    outline.assert_mmb_done()
}

// If any of the threads panic, just panic the whole thing since 
// the error is something to do with this tool rather than a user-provided input.
fn verify_par<'a>(outline: &'a Outline<'a>, num_threads: usize) -> Res<()> {
    let task_counter = AtomicUsize::new(0);

    thread::scope(|sco| {
        let mut mmb_tasks = Vec::new();

        for _ in 0..num_threads {
            mmb_tasks.push(sco.spawn(|_| verify_mmb(outline, &task_counter)));
        }

        sco
        .spawn(|_| verify_mmz(outline))
        .join()
        .unwrap()
        .map_err(|_| VerifErr::Msg(format!("mmz thread panicked!")))?;

        for (idx, mmb_task) in mmb_tasks.into_iter().enumerate() {
            mmb_task
            .join()
            .unwrap()
            .map_err(|_| VerifErr::Msg(format!("mmb thread # {} panicked", idx)))?;
        }
        Ok(())
    }).unwrap()
}


// Parsing/verifying the contents of the mmz file is done in serial
fn verify_mmz<'a>(outline: &'a Outline<'a>) -> Res<()> {
    let mut mem = MmzMem::new_from(outline).unwrap();
    let mut bump = Bump::new();
    for (stmt, _proof) in outline.declarations.iter() {
        localize!(mem.verify1(&mut bump, *stmt))?;
    }

    outline.assert_mmz_done(&mem)
}

fn verify_mmb<'a>(outline: &'a Outline<'a>, task_counter: &AtomicUsize) -> Res<()> {
    let mut bump = Bump::new();
    while let Some((stmt, proof)) = outline.declarations.get(task_counter.fetch_add(1, Relaxed)) {
        localize!(crate::mmb::MmbState::verify1(outline, &mut bump, *stmt, proof.clone()))?
    }
    Ok(())
}
