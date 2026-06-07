//! Weakest precondition computation.

use crate::{Assert, Expr, Stmt};

/// Compute the weakest precondition of a statement with respect to a postcondition.
///
/// WP rules:
/// - WP(skip, Q) = Q
/// - WP(x := e, Q) = Q[x/e]
/// - WP(S1; S2, Q) = WP(S1, WP(S2, Q))
/// - WP(if b then S1 else S2, Q) = (b → WP(S1, Q)) ∧ (¬b → WP(S2, Q))
/// - WP(while b inv I do S, Q) = I (with I as the invariant)
pub fn weakest_precondition(stmt: &Stmt, post: &Assert) -> Assert {
    match stmt {
        Stmt::Skip => post.clone(),
        Stmt::Assign { var, expr } => {
            // Q[x/e] — substitute var with expr in post
            let replacement = parse_simple_expr(expr);
            post.substitute(var, &replacement)
        }
        Stmt::Seq(s1, s2) => {
            let wp_s2 = weakest_precondition(s2, post);
            weakest_precondition(s1, &wp_s2)
        }
        Stmt::If { guard, then_branch, else_branch } => {
            let wp_then = weakest_precondition(then_branch, post);
            let wp_else = weakest_precondition(else_branch, post);
            let guard_assert = parse_simple_assert(guard);
            Assert::and(
                Assert::implies(guard_assert.clone(), wp_then),
                Assert::implies(Assert::not(guard_assert), wp_else),
            )
        }
        Stmt::While { invariant, guard, body } => {
            // For while loops, we use the invariant if provided
            if let Some(inv_str) = invariant {
                parse_simple_assert(inv_str)
            } else {
                // Without an invariant, we can't compute WP for loops
                // Return the postcondition as a fallback
                let guard_assert = parse_simple_assert(guard);
                let wp_body = weakest_precondition(body, post);
                Assert::and(
                    Assert::implies(guard_assert.clone(), wp_body),
                    Assert::implies(Assert::not(guard_assert), post.clone()),
                )
            }
        }
        Stmt::Assert(_) => post.clone(),
    }
}

/// Parse a simple expression string into an Expr.
/// Supports: variables, integer constants, and +, -, * operations.
pub fn parse_simple_expr(input: &str) -> Expr {
    let s = input.trim();

    // Try as integer constant
    if let Ok(n) = s.parse::<i64>() {
        return Expr::const_val(n);
    }

    // Check for binary operators at the top level (lowest precedence first)
    // Simple approach: scan for + or - at the top level
    let mut depth = 0;
    let mut last_add_sub = None;

    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            '+' if depth == 0 => last_add_sub = Some(i),
            '-' if depth == 0 && i > 0 => {
                // Make sure it's not a unary minus
                let prev = s.as_bytes()[i - 1];
                if prev != b' ' && prev != b'(' && prev != b'+' && prev != b'-' && prev != b'*' && prev != b'/' {
                    last_add_sub = Some(i);
                }
            }
            _ => {}
        }
    }

    if let Some(pos) = last_add_sub {
        let left = parse_simple_expr(&s[..pos]);
        let op_char = s.as_bytes()[pos];
        let right = parse_simple_expr(&s[pos + 1..]);
        return match op_char {
            b'+' => Expr::add(left, right),
            b'-' => Expr::sub(left, right),
            _ => Expr::add(left, right),
        };
    }

    // Check for * or /
    let mut last_mul_div = None;
    depth = 0;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            '*' | '/' if depth == 0 => last_mul_div = Some((i, c)),
            _ => {}
        }
    }

    if let Some((pos, op)) = last_mul_div {
        let left = parse_simple_expr(&s[..pos]);
        let right = parse_simple_expr(&s[pos + 1..]);
        return match op {
            '*' => Expr::mul(left, right),
            '/' => Expr::div(left, right),
            _ => Expr::mul(left, right),
        };
    }

    // Parenthesized expression
    if s.starts_with('(') && s.ends_with(')') {
        return parse_simple_expr(&s[1..s.len() - 1]);
    }

    // Must be a variable
    Expr::var(s)
}

/// Parse a simple assertion string.
/// Supports: comparisons (x > n, x < n, x = n, x >= n, x <= n) and logical connectives.
pub fn parse_simple_assert(input: &str) -> Assert {
    let s = input.trim();

    // Check for AND
    if let Some(pos) = s.find(" AND ").or_else(|| s.find(" and ")) {
        let left = parse_simple_assert(&s[..pos]);
        let right = parse_simple_assert(&s[pos + 5..]);
        return Assert::and(left, right);
    }

    // Check for OR
    if let Some(pos) = s.find(" OR ").or_else(|| s.find(" or ")) {
        let left = parse_simple_assert(&s[..pos]);
        let right = parse_simple_assert(&s[pos + 4..]);
        return Assert::or(left, right);
    }

    // Check for implication
    if let Some(pos) = s.find(" -> ") {
        let left = parse_simple_assert(&s[..pos]);
        let right = parse_simple_assert(&s[pos + 4..]);
        return Assert::implies(left, right);
    }

    // Check for NOT
    if s.starts_with("NOT ") || s.starts_with("not ") || s.starts_with("!") {
        let rest = if s.starts_with("!") { &s[1..] } else { &s[4..] };
        return Assert::not(parse_simple_assert(rest));
    }

    // Check for comparison operators
    for (op, len) in &[(">=", 2), ("<=", 2), ("!=", 2), (">", 1), ("<", 1), ("=", 1)] {
        if let Some(pos) = s.find(op) {
            let left = parse_simple_expr(&s[..pos]);
            let right = parse_simple_expr(&s[pos + len..]);
            return match *op {
                ">=" => Assert::Ge(left, right),
                "<=" => Assert::Le(left, right),
                "!=" => Assert::Neq(left, right),
                ">" => Assert::Gt(left, right),
                "<" => Assert::Lt(left, right),
                "=" => Assert::Eq(left, right),
                _ => Assert::Bool(true),
            };
        }
    }

    // Boolean constant
    match s {
        "true" | "TRUE" => Assert::tt(),
        "false" | "FALSE" => Assert::ff(),
        _ => Assert::tt(), // Default to true for unknown assertions
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wp_skip() {
        let post = Assert::gt("x", 0);
        let wp = weakest_precondition(&Stmt::skip(), &post);
        assert_eq!(wp, post);
    }

    #[test]
    fn test_wp_assign_simple() {
        // WP(x := 5, x > 0) = (5 > 0) = true
        let post = Assert::Gt(Expr::var("x"), Expr::const_val(0));
        let stmt = Stmt::assign("x", "5");
        let wp = weakest_precondition(&stmt, &post);
        // x is replaced with 5 in post, so 5 > 0
        let env = std::collections::HashMap::new();
        assert_eq!(wp.evaluate(&env), Some(true));
    }

    #[test]
    fn test_wp_assign_expr() {
        // WP(y := x + 1, y > x) = (x + 1 > x) = true
        let post = Assert::Gt(Expr::var("y"), Expr::const_val(0));
        let stmt = Stmt::assign("y", "x + 1");
        let wp = weakest_precondition(&stmt, &post);
        // y replaced by x + 1: (x + 1) > 0
        let mut env = std::collections::HashMap::new();
        env.insert("x".to_string(), 5);
        assert_eq!(wp.evaluate(&env), Some(true));
    }

    #[test]
    fn test_wp_sequence() {
        // WP(x := 1; x := x + 1, x > 1)
        // = WP(x := 1, WP(x := x+1, x > 1))
        // = WP(x := 1, x+1 > 1)
        // = 1+1 > 1 = true
        let post = Assert::Gt(Expr::var("x"), Expr::const_val(1));
        let stmt = Stmt::seq(
            Stmt::assign("x", "1"),
            Stmt::assign("x", "x + 1"),
        );
        let wp = weakest_precondition(&stmt, &post);
        let env = std::collections::HashMap::new();
        assert_eq!(wp.evaluate(&env), Some(true));
    }

    #[test]
    fn test_wp_conditional() {
        // WP(if x > 0 then y := 1 else y := -1, y > 0)
        // = (x > 0 → 1 > 0) ∧ (¬(x > 0) → -1 > 0)
        // = (x > 0 → true) ∧ (¬(x > 0) → false)
        let post = Assert::Gt(Expr::var("y"), Expr::const_val(0));
        let stmt = Stmt::if_then_else(
            "x > 0",
            Stmt::assign("y", "1"),
            Stmt::assign("y", "-1"),
        );
        let wp = weakest_precondition(&stmt, &post);

        let mut env = std::collections::HashMap::new();
        env.insert("x".to_string(), 5);
        assert_eq!(wp.evaluate(&env), Some(true));

        env.insert("x".to_string(), -5);
        assert_eq!(wp.evaluate(&env), Some(false));
    }

    #[test]
    fn test_parse_expr() {
        assert_eq!(parse_simple_expr("42"), Expr::const_val(42));
        assert_eq!(parse_simple_expr("x"), Expr::var("x"));
        assert_eq!(parse_simple_expr("x + 1"), Expr::add(Expr::var("x"), Expr::const_val(1)));
    }

    #[test]
    fn test_parse_assert() {
        let a = parse_simple_assert("x > 0");
        let mut env = std::collections::HashMap::new();
        env.insert("x".to_string(), 5);
        assert_eq!(a.evaluate(&env), Some(true));
    }

    #[test]
    fn test_parse_assert_conjunction() {
        let a = parse_simple_assert("x > 0 AND x < 10");
        let mut env = std::collections::HashMap::new();
        env.insert("x".to_string(), 5);
        assert_eq!(a.evaluate(&env), Some(true));
        env.insert("x".to_string(), 15);
        assert_eq!(a.evaluate(&env), Some(false));
    }

    #[test]
    fn test_wp_while_with_invariant() {
        let post = Assert::Ge(Expr::var("x"), Expr::const_val(0));
        let stmt = Stmt::while_with_inv(
            "x > 0",
            "x >= 0",
            Stmt::assign("x", "x - 1"),
        );
        let wp = weakest_precondition(&stmt, &post);
        // With invariant, WP should be the invariant
        let mut env = std::collections::HashMap::new();
        env.insert("x".to_string(), 5);
        assert_eq!(wp.evaluate(&env), Some(true));
    }
}
