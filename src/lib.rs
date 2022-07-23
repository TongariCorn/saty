use dimacs::{Clause, Sign, Lit};
mod types;
use types::*;

#[macro_use] extern crate log;
extern crate simplelog;

pub enum SATResult {
    SAT(Vec<LBool>),
    UNSAT
}

pub fn print_clauses(clauses: &Box<[Clause]>) -> String {
    let mut str = String::from("");
    for i in 0..clauses.len() {
        let clause = &clauses[i];
        str += "(";
        for j in 0..clause.lits().len() {
            match clause.lits()[j].sign() {
                Sign::Pos => (),
                Sign::Neg => str += "-"
            }
            str = format!("{}x{}", str, clause.lits()[j].var().to_u64());

            if j == clause.lits().len()-1 {
                str += ")";
            } else {
                str += " v ";
            }
        }
        if i < clauses.len()-1 {
            str += " /\\ ";
        }
    }
    return str
}

pub fn print_result(assigns: &Vec<LBool>) -> String {
    let mut str = String::from("[");
    for i in 1..assigns.len() {
        str = format!("{} x{} = {}", str, i, match assigns[i] {
            LBool::TRUE => "true",
            _           => "false"  // LBool::BOTTOM can take arbitrary value
        })
    }
    str += "]";
    return str
}

pub fn solve_sat(clauses: Box<[Clause]>, num_vars: u64 ) -> SATResult {
    info!("{:?}", clauses);
    info!("num_vars = {}", num_vars);

    // Propositional variable indices in dimacs start at 1
    let num_vars: usize = num_vars.try_into().unwrap();
    let mut assigns  : Vec<LBool> = Vec::with_capacity(num_vars+1); // index 0 corresponds to bottom
    let mut trail    : Vec<Trail> = Vec::with_capacity(num_vars);   // assigned/implied literals in chronological order
    let mut trail_id : Vec<usize> = Vec::with_capacity(num_vars+1); // index in assigns -> index in trail
    let mut level    : Vec<i64>   = Vec::with_capacity(num_vars+1); // separator indices for different decision levels in trail
    let mut learnt_clauses: Vec<Clause> = Vec::new();
    assigns.resize_with(num_vars+1, Default::default);
    trail_id.resize_with(num_vars+1, Default::default);
    level.push(-1); // for simplicity, element at index -1 in trail vector is assumed to be at decision level 0


    loop {
        if !decide(&mut assigns, &mut trail, &mut trail_id, &mut level) {
            let result = assigns.clone();
            return SATResult::SAT(result)
        }
        while !boolean_constraint_propagation(&clauses, &learnt_clauses, &mut assigns, &mut trail, &mut trail_id) {
            if !resolve_conflict(&mut learnt_clauses, &mut assigns, &mut trail, &mut trail_id, &mut level) {
                return SATResult::UNSAT
            }
        }
    }
}

fn boolean_constraint_propagation_for_clause(clause: &Clause, assigns: &mut Vec<LBool>, trail: &mut Vec<Trail>, trail_id: &mut Vec<usize>) -> usize {
    // conflict occurs   -> 0
    // assignment occurs -> 1
    // otherwise         -> 2
    let mut unassigned_exist = false;
    let mut unassigned_id = 0;
    for j in 0..clause.len() {
        let curr_id: usize =  clause.lits()[j].var().to_u64().try_into().unwrap();
        let literal_valeu = match clause.lits()[j].sign() { Sign::Pos => assigns[curr_id], Sign::Neg => negate(assigns[curr_id]) };
        match literal_valeu {
            LBool::TRUE => {
                // This clause is true
                info!("{:?} is true", clause);
                return 2
            },
            LBool::FALSE => {
                ()
            },
            LBool::BOTTOM => {
                if unassigned_exist {
                    // there are more than one unassigned variables in this clause
                    info!("There are more than one unassigned variables in {:?}", clause);
                    return 2
                }
                unassigned_exist = true;
                unassigned_id = j;
            }
        }
    }
    if unassigned_exist {   // this clause is unit
        let curr_id: usize =  clause.lits()[unassigned_id].var().to_u64().try_into().unwrap();
        info!("{:?} is unit, and a variable {} is implied", clause, curr_id);
        assigns[curr_id] = match clause.lits()[unassigned_id].sign() {
            Sign::Pos => LBool::TRUE,
            Sign::Neg => LBool::FALSE
        };
        trail.push(Trail::new_implied_trail(clause.lits()[unassigned_id], clause.clone()));
        trail_id[curr_id] = trail.len()-1;

        // new assignment happens, so repeat boolean propagation from start
        return 1
    } else {    // all literals are false, and conflict occurs
        info!("Conflict occurs in {:?}", clause);
        trail.push(Trail::new_bottom_trail(clause.clone()));
        trail_id[0] = trail.len()-1;
        return 0
    }
}

fn boolean_constraint_propagation(clauses: &Box<[Clause]>, learnt_clauses: &Vec<Clause>, assigns: &mut Vec<LBool>, trail: &mut Vec<Trail>, trail_id: &mut Vec<usize>) -> bool {
    // there are no more implications -> true
    // conflict is produced           -> false
    info!("Start boolean constraint propagation");
    'restart: loop {
        info!("assigns: {:?}", assigns);
        info!("trail: {:?}", trail);
        info!("trail_id: {:?}", trail_id);
        info!("learnt clauses: {:?}", learnt_clauses);

        for i in 0..learnt_clauses.len() {
            let clause = &learnt_clauses[i];
            info!("target clause: {:?}", clause);

            match boolean_constraint_propagation_for_clause(clause, assigns, trail, trail_id) {
                0 => return false,
                1 => continue 'restart,
                _ => ()
            }
        }

        for i in 0..clauses.len() {
            let clause = &clauses[i];
            info!("{:?}", clause);

            match boolean_constraint_propagation_for_clause(clause, assigns, trail, trail_id) {
                0 => return false,
                1 => continue 'restart,
                _ => ()
            }
        }
        break;
    }
    return true
}

// select a variable that is not currently assigned, and give it a value
fn decide(assigns: &mut Vec<LBool>, trail: &mut Vec<Trail>, trail_id: &mut Vec<usize>, level: &mut Vec<i64>) -> bool {
    // there are no more unassigned variables -> false
    // otherwise                              -> true
    for i in 1..assigns.len() {
        match assigns[i] {
            LBool::BOTTOM => {
                assigns[i] = LBool::TRUE;
                trail.push(Trail::new_assigned_trail(i, true));
                trail_id[i] = trail.len()-1;
                level.push(trail.len() as i64 - 1);

                info!("Decide: x{} is assigned to be true", i);
                return true
            },
            _ => ()
        }
    }
    info!("Decide: there are no more unassigned variables");
    return false
}

fn resolve_conflict(learnt_clauses: &mut Vec<Clause>, assigns: &mut Vec<LBool>, trail: &mut Vec<Trail>, trail_id: &mut Vec<usize>, level: &mut Vec<i64>) -> bool {
    info!("Resolve conflict");
    if level.len() == 1 {    // current decision level is 0, so this proposition is unsatisfiable
        return false
    }
    info!("trail: {:?}", trail);
    info!("level: {:?}", level);

    let mut learnt_vertex: Vec<usize> = Vec::new(); // list of index w.r.t. trail vector
    learnt_vertex.push(trail_id[0]); // Initialize learnt_vertex with bottom, whose index is 0
    
    // There is a UIP at decision level d, when the number of literals in learnt_vertex
    // assigned at decision level d is 1.
    loop {

        let last_trail = &trail[*learnt_vertex.last().unwrap()];
        let last_vertex = last_trail.literal.var();
        match &last_trail.trail_type {
            TrailType::AssignedTrail => {   // This should be one and only one literal in learnt_vertex assigned at decision level d
            },
            TrailType::ImpliedTrail(clause) => {
                for lit in clause.lits() {
                    learnt_vertex.push(trail_id[lit.var().to_u64() as usize]);
                }
                learnt_vertex.sort();
                learnt_vertex.dedup();
                learnt_vertex.retain(|vertex| trail[*vertex].literal.var() != last_vertex);

                info!("learnt_vertex: {:?}", learnt_vertex);
                if learnt_vertex.len() == 1 || (learnt_vertex[learnt_vertex.len() - 2] as i64) < *level.last().unwrap() {
                    // found UIP, so construct a learnt clause from learnt_vertex
                    // backjump to the second largest decision level
                    let back_level = if learnt_vertex.len() == 1 { 0 } else { 
                        // check the second largest decision level among learnt_vertex
                        let mut l = 0;
                        for dl in (0..level.len()-1).rev() {
                            if level[dl] < learnt_vertex[learnt_vertex.len() - 2] as i64 {
                                l = dl;
                                break;
                            }
                        }
                        l
                    };
                    info!("backjump to level {:?}", back_level);

                    let mut learnt_clause: Vec<Lit> = Vec::new();
                    for vertex in learnt_vertex {
                        learnt_clause.push(negate_literal(trail[vertex].literal));
                    }
                    let learnt_clause = Clause::from_vec(learnt_clause);
                    info!("learnt clause: {:?}", learnt_clause);
                    learnt_clauses.push(learnt_clause);

                    for t in &trail[level[back_level+1] as usize..] {
                        let index = t.literal.var().to_u64() as usize;
                        assigns[index] = LBool::BOTTOM;
                        trail_id[index] = 0;
                    }
                    trail.truncate(level[back_level+1] as usize);
                    level.truncate(back_level+1);

                    info!("trail: {:?}", trail);
                    info!("assign: {:?}", assigns);
                    info!("level: {:?}", level);

                    return true
                }
            }
        }
    }
}
