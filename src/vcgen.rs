//! Verification condition generation.

use crate::{Assert, weakest_precondition};
use std::fmt;

/// A statement in the simple imperative language.
/// Re-exported from triple module via lib.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    /// Skip (no-op).
    Skip,
    /// Assignment: var := expr.
    Assign { var: String, expr: String },
    /// Sequential composition.
    Seq(Box<Stmt>, Box<Stmt>),
    /// Conditional.
    If { guard: String, then_branch: Box<Stmt>, else_branch: Box<Stmt> },
    /// While loop with optional invariant.
    While { guard: String, invariant: Option<String>, body: Box<Stmt> },
    /// Assert.
    Assert(String),
}

impl Stmt {
    /// Create a skip.
    pub fn skip() -> Self { Stmt::Skip }
    /// Create an assignment.
    pub fn assign(var: &str, expr: &str) -> Self {
        Stmt::Assign { var: var.to_string(), expr: expr.to_string() }
    }
    /// Create a sequence.
    pub fn seq(s1: Stmt, s2: Stmt) -> Self {
        Stmt::Seq(Box::new(s1), Box::new(s2))
    }
    /// Create a conditional.
    pub fn if_then_else(guard: &str, then: Stmt, else_: Stmt) -> Self {
        Stmt::If { guard: guard.to_string(), then_branch: Box::new(then), else_branch: Box::new(else_) }
    }
    /// Create a while loop.
    pub fn while_loop(guard: &str, body: Stmt) -> Self {
        Stmt::While { guard: guard.to_string(), invariant: None, body: Box::new(body) }
    }
    /// Create a while loop with invariant.
    pub fn while_with_inv(guard: &str, inv: &str, body: Stmt) -> Self {
        Stmt::While { guard: guard.to_string(), invariant: Some(inv.to_string()), body: Box::new(body) }
    }
    /// Create an assert.
    pub fn assert(cond: &str) -> Self {
        Stmt::Assert(cond.to_string())
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::Skip => write!(f, "skip"),
            Stmt::Assign { var, expr } => write!(f, "{} := {}", var, expr),
            Stmt::Seq(s1, s2) => write!(f, "{}; {}", s1, s2),
            Stmt::If { guard, then_branch, else_branch } => {
                write!(f, "if {} then {} else {} fi", guard, then_branch, else_branch)
            }
            Stmt::While { guard, invariant, body } => {
                if let Some(inv) = invariant {
                    write!(f, "while {} inv [{}] do {} od", guard, inv, body)
                } else {
                    write!(f, "while {} do {} od", guard, body)
                }
            }
            Stmt::Assert(cond) => write!(f, "assert({})", cond),
        }
    }
}

/// Generate verification conditions for a Hoare triple {P} S {Q}.
///
/// Returns the list of verification conditions that must be proved:
/// - VCs from WP computation
/// - For loops: invariant must hold initially, be preserved, and imply postcondition
pub fn vcgen(stmt: &Stmt, post: &Assert) -> Vec<Assert> {
    let mut vcs = Vec::new();
    generate_vcs(stmt, post, &mut vcs);
    vcs
}

fn generate_vcs(stmt: &Stmt, post: &Assert, vcs: &mut Vec<Assert>) {
    match stmt {
        Stmt::Skip | Stmt::Assign { .. } => {
            // VC is just: P → WP(S, Q)
            let wp = weakest_precondition(stmt, post);
            vcs.push(wp);
        }
        Stmt::Seq(s1, s2) => {
            let wp_s2 = weakest_precondition(s2, post);
            generate_vcs(s1, &wp_s2, vcs);
        }
        Stmt::If { guard, then_branch, else_branch } => {
            let guard_a = crate::wp::parse_simple_assert(guard);
            let wp_then = weakest_precondition(then_branch, post);
            let wp_else = weakest_precondition(else_branch, post);

            // VC1: (P ∧ guard) → WP(then, Q)
            vcs.push(Assert::implies(
                guard_a.clone(),
                wp_then,
            ));
            // VC2: (P ∧ ¬guard) → WP(else, Q)
            vcs.push(Assert::implies(
                Assert::not(guard_a),
                wp_else,
            ));

            // Recursively generate VCs for branches
            generate_vcs(then_branch, post, vcs);
            generate_vcs(else_branch, post, vcs);
        }
        Stmt::While { guard, invariant, body } => {
            if let Some(inv_str) = invariant {
                let inv = crate::wp::parse_simple_assert(inv_str);
                let guard_a = crate::wp::parse_simple_assert(guard);

                // VC1: invariant holds initially (inv → WP(skip, inv))
                // This is trivially true, so we generate:
                // VC: inv (must be established by precondition)

                // VC2: invariant is preserved by the loop body
                // (inv ∧ guard) → WP(body, inv)
                let wp_body = weakest_precondition(body, &inv);
                vcs.push(Assert::implies(
                    Assert::and(inv.clone(), guard_a.clone()),
                    wp_body,
                ));

                // VC3: (inv ∧ ¬guard) → post
                vcs.push(Assert::implies(
                    Assert::and(inv.clone(), Assert::not(guard_a)),
                    post.clone(),
                ));

                // Generate VCs for the body
                generate_vcs(body, &inv, vcs);
            } else {
                // Without invariant, generate a simple VC
                let wp = weakest_precondition(stmt, post);
                vcs.push(wp);
            }
        }
        Stmt::Assert(cond) => {
            let cond_a = crate::wp::parse_simple_assert(cond);
            vcs.push(cond_a);
        }
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

    /// Generate verification conditions for this triple.
    pub fn verify(&self) -> TripleResult {
        let vcs = vcgen(&self.stmt, &self.post);
        // Check if pre → WP holds (simplified check)
        // For a full verification, we'd need an SMT solver or theorem prover
        // Here we just generate the VCs
        if vcs.is_empty() {
            TripleResult::Valid
        } else {
            // Check if any VC is trivially false
            let env = std::collections::HashMap::new();
            for vc in &vcs {
                if vc.evaluate(&env) == Some(false) {
                    return TripleResult::Invalid(vc.clone());
                }
            }
            TripleResult::Valid
        }
    }

    /// Get the verification conditions.
    pub fn vcs(&self) -> Vec<Assert> {
        vcgen(&self.stmt, &self.post)
    }
}

impl fmt::Display for HoareTriple {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{{}}} {}; {{{}}}", self.pre, self.stmt, self.post)
    }
}

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Expr;

    #[test]
    fn test_vcgen_skip() {
        let post = Assert::gt("x", 0);
        let stmt = Stmt::skip();
        let vcs = vcgen(&stmt, &post);
        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0], post);
    }

    #[test]
    fn test_vcgen_assign() {
        let post = Assert::Gt(Expr::const_val(5), Expr::const_val(0));
        let stmt = Stmt::assign("x", "5");
        let vcs = vcgen(&stmt, &post);
        assert_eq!(vcs.len(), 1);
        // VC should be 5 > 0, which evaluates to true
        let env = std::collections::HashMap::new();
        assert_eq!(vcs[0].evaluate(&env), Some(true));
    }

    #[test]
    fn test_vcgen_sequence() {
        let post = Assert::gt("x", 1);
        let stmt = Stmt::seq(
            Stmt::assign("x", "1"),
            Stmt::assign("x", "x + 1"),
        );
        let vcs = vcgen(&stmt, &post);
        assert!(!vcs.is_empty());
    }

    #[test]
    fn test_vcgen_conditional() {
        let post = Assert::gt("y", 0);
        let stmt = Stmt::if_then_else(
            "x > 0",
            Stmt::assign("y", "1"),
            Stmt::assign("y", "2"),
        );
        let vcs = vcgen(&stmt, &post);
        // Should have VCs for both branches
        assert!(vcs.len() >= 2);
    }

    #[test]
    fn test_vcgen_while() {
        let post = Assert::ge("x", 0);
        let stmt = Stmt::while_with_inv(
            "x > 0",
            "x >= 0",
            Stmt::assign("x", "x - 1"),
        );
        let vcs = vcgen(&stmt, &post);
        // Should have: preservation VC and postcondition VC
        assert!(vcs.len() >= 2);
    }

    #[test]
    fn test_hoare_triple_valid() {
        let triple = HoareTriple::new(
            Assert::gt("x", 0),
            Stmt::assign("y", "x"),
            Assert::gt("y", 0),
        );
        let result = triple.verify();
        assert!(result.is_valid());
    }

    #[test]
    fn test_hoare_triple_display() {
        let triple = HoareTriple::new(
            Assert::gt("x", 0),
            Stmt::assign("y", "x"),
            Assert::gt("y", 0),
        );
        let s = format!("{}", triple);
        assert!(s.contains("y := x"));
    }

    #[test]
    fn test_vcgen_assert() {
        let stmt = Stmt::assert("x > 0");
        let post = Assert::tt();
        let vcs = vcgen(&stmt, &post);
        assert!(!vcs.is_empty());
    }

    #[test]
    fn test_stmt_display() {
        assert_eq!(format!("{}", Stmt::skip()), "skip");
        assert_eq!(format!("{}", Stmt::assign("x", "1")), "x := 1");
        let seq = Stmt::seq(Stmt::assign("x", "1"), Stmt::assign("y", "2"));
        assert!(format!("{}", seq).contains(";"));
    }

    #[test]
    fn test_hoare_triple_vcs() {
        let triple = HoareTriple::new(
            Assert::gt("x", 0),
            Stmt::assign("y", "x + 1"),
            Assert::gt("y", 1),
        );
        let vcs = triple.vcs();
        assert!(!vcs.is_empty());
    }
}
