use std::env;
use std::fs;
use std::fs::File;
use dimacs::parse_dimacs;
use saty::SATResult;

#[macro_use] extern crate log;
extern crate simplelog;
use simplelog::*;

fn main() {
    CombinedLogger::init(
        vec![
            TermLogger::new(LevelFilter::Warn, Config::default(), TerminalMode::Mixed, ColorChoice::Auto),
            WriteLogger::new(LevelFilter::Info, Config::default(), File::create("solver.log").unwrap()),
        ]
    ).unwrap();

    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        error!("Filename should be specified.");
        return
    }
    let filename = &args[1];
    let str = fs::read_to_string(filename).expect("Something went wrong reading the file");
    println!("{}", &str);
    
    let result = parse_dimacs(&str);

    match result.unwrap() {
        dimacs::Instance::Cnf { clauses, num_vars } => { 
            println!("{}", saty::print_clauses(&clauses));
            let result = saty::solve_sat(clauses, num_vars);
            match result {
                SATResult::SAT(assigns) => {
                    println!("satisfiable with {:?}", saty::print_result(&assigns));
                    info!("satisfiable with {:?}", saty::print_result(&assigns));
                },
                SATResult::UNSAT => {
                    println!("unsatisfiable");
                    info!("unsatisfiable");
                }
            };
        },
        _  => ()
    }
}
