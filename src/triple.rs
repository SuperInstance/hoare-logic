//! Hoare triple representation and validity checking.

use crate::vcgen::Stmt;
use crate::Assert;
use std::fmt;

/// Result of verifying a Hoare triple.
#[derive(Clone, Debug)]
pub enum TripleResult {
    /// The triple is valid (all VCs hold).
    Valid,
    /// The triple is invalid with a failing VC.
    Invalid(Assert),
}

impl TripleResult {
    /// Whether the triple is valid.
    pub fn is_valid(&self) -> bool {
        matches!(self, TripleResult::Valid)
    }
}

/// A Hoare triple {P} S {Q}.
#[derive(Clone, Debug)]
pub struct HoareTriple {
    /// Precondition.
    pub pre: Assert,
    /// Statement.
    pub stmt: Stmt,
    /// Postcondition.
    pub post: Assert,
}

impl HoareTriple {
    /// Create a new Hoare triple.
    pub fn new(pre: Assert, stmt: Stmt, post: Assert) -> Self {
        HoareTriple { pre, stmt, post }
    }
}

impl fmt::Display for HoareTriple {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{{}}} {}; {{{}}}", self.pre, self.stmt, self.post)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Expr, vcgen};

    #[test]
    fn test_triple_creation() {
        let triple = HoareTriple::new(
            Assert::gt("x", 0),
            Stmt::assign("x", "5"),
            Assert::Gt(Expr::var("x"), Expr::const_val(0)),
        );
        assert!(format!("{}", triple).contains("x := 5"));
    }

    #[test]
    fn test_triple_result_valid() {
        let r = TripleResult::Valid;
        assert!(r.is_valid());
    }

    #[test]
    fn test_triple_result_invalid() {
        let r = TripleResult::Invalid(Assert::ff());
        assert!(!r.is_valid());
    }
}
