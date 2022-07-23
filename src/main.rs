use dimacs::parse_dimacs;
use saty::SATResult;

fn main() {
    println!("Hello, world!");
    
    let str = "c Example CNF format file
c
p cnf 4 3
1 3 -4 0
4 0 2
-3";
    let str = "p cnf 5 4
1 2 0 3
4 5 0
-2 0";
    let str = "p cnf 5 6
1 -2 0
-1 3 -4 0
1 3 -4 0
-3 -5 0
-3 5 0
3 4";
    let str = "p cnf 5 5
1 -2 0
1 3 -4 0
-3 -5 0
-3 5 0
3 4";

    let result = parse_dimacs(str);

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
