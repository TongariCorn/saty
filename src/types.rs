use std::fmt;
use dimacs::{Clause, Sign, Lit};

#[derive(Copy, Clone)]
pub enum LBool {
    TRUE,
    FALSE,
    BOTTOM
}

pub fn negate(l: LBool) -> LBool {
    return match l {
        LBool::TRUE  => LBool::FALSE,
        LBool::FALSE => LBool::TRUE,
        _            => LBool::BOTTOM
    }
}

pub fn negate_literal(l: Lit) -> Lit {
    return match l.sign() {
        Sign::Pos => Lit::from_i64(-(l.var().to_u64() as i64)),
        Sign::Neg => Lit::from_i64(l.var().to_u64() as i64)
    }
}

impl fmt::Debug for LBool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LBool::TRUE   => write!(f, "TRUE"),
            LBool::FALSE  => write!(f, "FALSE"),
            LBool::BOTTOM => write!(f, "BOTTOM")
        }
    }
}

impl Default for LBool {
    fn default() -> Self { LBool::BOTTOM }
}

pub enum TrailType {
    AssignedTrail,
    ImpliedTrail(Clause)
}

pub struct Trail {
    pub trail_type: TrailType,
    pub literal   : Lit
}

impl Trail {
    pub fn new_assigned_trail(id: usize, value: bool) -> Self {
        let id:i64 = id.try_into().unwrap();
        let lit = Lit::from_i64(if value { id } else { -id });
        return Trail { trail_type: TrailType::AssignedTrail, literal: lit }
    }

    pub fn new_implied_trail(literal: Lit, clause: Clause) -> Self {
        return Trail { trail_type: TrailType::ImpliedTrail(clause), literal: literal }
    }

    pub fn new_bottom_trail(clause: Clause) -> Self {
        let lit = Lit::from_i64(0); // bottom literal
        return Trail { trail_type: TrailType::ImpliedTrail(clause), literal: lit }
    }
}

impl fmt::Debug for Trail {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.trail_type {
            TrailType::AssignedTrail        => write!(f, "Assigned {:?}", self.literal),
            TrailType::ImpliedTrail(clause) => write!(f, "{:?} implied by {:?}", self.literal, clause),
        }
    }
}

