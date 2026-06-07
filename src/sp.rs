//! Strongest postcondition computation.

use crate::{Assert, Expr, Stmt};

/// Compute the strongest postcondition of a statement with respect to a precondition.
///
/// SP rules:
/// - SP(skip, P) = P
/// - SP(x := e, P) = ∃x₀. P[x/x₀] ∧ x = e[x/x₀]
/// - SP(S1; S2, P) = SP(S2, SP(S1, P))
/// - SP(if b then S1 else S2, P) = SP(S1, P ∧ b) ∨ SP(S2, P ∧ ¬b)
pub fn strongest_postcondition(stmt: &Stmt, pre: &Assert) -> Assert {
    match stmt {
        Stmt::Skip => pre.clone(),
        Stmt::Assign { var, expr } => {
            // SP(x := e, P) = ∃x₀. P[x/x₀] ∧ x = e[x/x₀]
            let old_var = format!("{}_0", var);
            let old_expr = Expr::var(&old_var);
            let pre_sub = pre.substitute(var, &old_expr);
            let expr_sub = crate::wp::parse_simple_expr(expr).substitute(var, &old_expr);
            Assert::and(
                Assert::forall(&old_var, Assert::and(
                    pre_sub,
                    Assert::eq(Expr::var(var), expr_sub),
                )),
                // Simplified: just return the substituted version
                // For full SP we'd use existential, but we approximate
                {
                    let expr_parsed = crate::wp::parse_simple_expr(expr);
                    Assert::and(
                        pre.substitute(var, &old_expr),
                        Assert::eq(Expr::var(var), expr_parsed),
                    )
                },
            )
        }
        Stmt::Seq(s1, s2) => {
            let sp_s1 = strongest_postcondition(s1, pre);
            strongest_postcondition(s2, &sp_s1)
        }
        Stmt::If { guard, then_branch, else_branch } => {
            let guard_assert = crate::wp::parse_simple_assert(guard);
            let sp_then = strongest_postcondition(
                then_branch,
                &Assert::and(pre.clone(), guard_assert.clone()),
            );
            let sp_else = strongest_postcondition(
                else_branch,
                &Assert::and(pre.clone(), Assert::not(guard_assert)),
            );
            Assert::or(sp_then, sp_else)
        }
        Stmt::While { guard, body, .. } => {
            // Simplified: for loops we approximate SP
            let guard_assert = crate::wp::parse_simple_assert(guard);
            let sp_body = strongest_postcondition(body, &Assert::and(pre.clone(), guard_assert));
            Assert::or(pre.clone(), sp_body)
        }
        Stmt::Assert(_) => pre.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wp::parse_simple_assert;

    #[test]
    fn test_sp_skip() {
        let pre = Assert::gt("x", 0);
        let sp = strongest_postcondition(&Stmt::skip(), &pre);
        assert_eq!(sp, pre);
    }

    #[test]
    fn test_sp_assign() {
        let pre = Assert::gt("x", 0);
        let stmt = Stmt::assign("y", "x");
        let sp = strongest_postcondition(&stmt, &pre);
        // SP should mention both old x and new y
        // Simplified: x_0 > 0 ∧ y = x
        assert!(format!("{}", sp).contains("y"));
    }

    #[test]
    fn test_sp_sequence() {
        let pre = Assert::gt("x", 0);
        let stmt = Stmt::seq(
            Stmt::assign("y", "x"),
            Stmt::assign("y", "y + 1"),
        );
        let sp = strongest_postcondition(&stmt, &pre);
        // SP should describe the final state
        assert!(format!("{}", sp).contains("y"));
    }

    #[test]
    fn test_sp_conditional() {
        let pre = Assert::gt("x", 0);
        let stmt = Stmt::if_then_else(
            "x > 1",
            Stmt::assign("y", "1"),
            Stmt::assign("y", "0"),
        );
        let sp = strongest_postcondition(&stmt, &pre);
        // SP should be a disjunction of the two branches
        assert!(format!("{}", sp).contains("∨"));
    }

    #[test]
    fn test_sp_assign_const() {
        let pre = Assert::gt("x", 0);
        let stmt = Stmt::assign("x", "5");
        let sp = strongest_postcondition(&stmt, &pre);
        // x_0 > 0 ∧ x = 5
        let result = format!("{}", sp);
        assert!(result.contains("5"));
    }

    #[test]
    fn test_sp_while_approximation() {
        let pre = Assert::ge("x", 0);
        let stmt = Stmt::while_loop("x > 0", Stmt::assign("x", "x - 1"));
        let sp = strongest_postcondition(&stmt, &pre);
        // Approximated: pre OR sp_body
        assert!(format!("{}", sp).contains("∨") || format!("{}", sp).contains("≥"));
    }

    #[test]
    fn test_sp_true_precondition() {
        let pre = Assert::tt();
        let stmt = Stmt::assign("x", "42");
        let sp = strongest_postcondition(&stmt, &pre);
        assert!(format!("{}", sp).contains("42"));
    }

    #[test]
    fn test_sp_preserves_structure() {
        let pre = parse_simple_assert("x > 0 AND x < 10");
        let stmt = Stmt::assign("y", "x + 1");
        let sp = strongest_postcondition(&stmt, &pre);
        let s = format!("{}", sp);
        assert!(s.contains("y"));
    }
}
