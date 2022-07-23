use std::env;
use std::fs;
use dimacs::parse_dimacs;
use saty::SATResult;

fn main() {
    let args: Vec<String> = env::args().collect();
    let filename = &args[1];
    let str = fs::read_to_string(filename).expect("Something went wrong reading the file");
    println!("{}", &str);
    
    let result = parse_dimacs(&str);

    match result.unwrap() {
        dimacs::Instance::Cnf { clauses, num_vars } => { 
            let result = saty::solve_sat(clauses, num_vars);
            match result {
                SATResult::SAT(assigns) => println!("satisfiable with {:?}", &assigns[1..assigns.len()]),
                SATResult::UNSAT => println!("unsatisfiable")
            };
        },
        _  => ()
    }
}
