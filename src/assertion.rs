//! Assertion language for Hoare logic.

use std::fmt;

/// An arithmetic expression.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expr {
    /// Integer constant.
    Const(i64),
    /// Variable reference.
    Var(String),
    /// Binary operation.
    BinOp(BinExpr, Box<Expr>, Box<Expr>),
    /// Negation (unary minus).
    Neg(Box<Expr>),
}

/// Binary expression operators.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinExpr {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

impl Expr {
    /// Integer constant.
    pub fn const_val(n: i64) -> Self {
        Expr::Const(n)
    }

    /// Variable reference.
    pub fn var(name: &str) -> Self {
        Expr::Var(name.to_string())
    }

    /// Addition.
    pub fn add(l: Expr, r: Expr) -> Self {
        Expr::BinOp(BinExpr::Add, Box::new(l), Box::new(r))
    }

    /// Subtraction.
    pub fn sub(l: Expr, r: Expr) -> Self {
        Expr::BinOp(BinExpr::Sub, Box::new(l), Box::new(r))
    }

    /// Multiplication.
    pub fn mul(l: Expr, r: Expr) -> Self {
        Expr::BinOp(BinExpr::Mul, Box::new(l), Box::new(r))
    }

    /// Division.
    pub fn div(l: Expr, r: Expr) -> Self {
        Expr::BinOp(BinExpr::Div, Box::new(l), Box::new(r))
    }

    /// Negation.
    pub fn neg(e: Expr) -> Self {
        Expr::Neg(Box::new(e))
    }

    /// Substitute variable `name` with expression `replacement`.
    pub fn substitute(&self, name: &str, replacement: &Expr) -> Expr {
        match self {
            Expr::Const(_) => self.clone(),
            Expr::Var(n) if n == name => replacement.clone(),
            Expr::Var(_) => self.clone(),
            Expr::BinOp(op, l, r) => Expr::BinOp(
                *op,
                Box::new(l.substitute(name, replacement)),
                Box::new(r.substitute(name, replacement)),
            ),
            Expr::Neg(e) => Expr::Neg(Box::new(e.substitute(name, replacement))),
        }
    }

    /// Collect all variable names.
    pub fn variables(&self) -> Vec<String> {
        let mut vars = Vec::new();
        self.collect_vars(&mut vars);
        vars.sort();
        vars.dedup();
        vars
    }

    fn collect_vars(&self, vars: &mut Vec<String>) {
        match self {
            Expr::Const(_) => {}
            Expr::Var(n) => {
                if !vars.contains(n) {
                    vars.push(n.clone());
                }
            }
            Expr::BinOp(_, l, r) => {
                l.collect_vars(vars);
                r.collect_vars(vars);
            }
            Expr::Neg(e) => e.collect_vars(vars),
        }
    }

    /// Evaluate the expression given variable bindings.
    pub fn evaluate(&self, env: &std::collections::HashMap<String, i64>) -> Option<i64> {
        match self {
            Expr::Const(n) => Some(*n),
            Expr::Var(n) => env.get(n).copied(),
            Expr::BinOp(op, l, r) => {
                let lv = l.evaluate(env)?;
                let rv = r.evaluate(env)?;
                Some(match op {
                    BinExpr::Add => lv.wrapping_add(rv),
                    BinExpr::Sub => lv.wrapping_sub(rv),
                    BinExpr::Mul => lv.wrapping_mul(rv),
                    BinExpr::Div => {
                        if rv == 0 { return None; }
                        lv.wrapping_div(rv)
                    }
                    BinExpr::Mod => {
                        if rv == 0 { return None; }
                        lv.wrapping_rem(rv)
                    }
                })
            }
            Expr::Neg(e) => Some(-e.evaluate(env)?),
        }
    }

    /// Simplify constant sub-expressions.
    pub fn simplify(&self) -> Expr {
        match self {
            Expr::Const(_) | Expr::Var(_) => self.clone(),
            Expr::BinOp(op, l, r) => {
                let ls = l.simplify();
                let rs = r.simplify();
                match (&ls, &rs) {
                    (Expr::Const(a), Expr::Const(b)) => Expr::Const(match op {
                        BinExpr::Add => a.wrapping_add(*b),
                        BinExpr::Sub => a.wrapping_sub(*b),
                        BinExpr::Mul => a.wrapping_mul(*b),
                        BinExpr::Div => {
                            if *b == 0 { return Expr::BinOp(*op, Box::new(ls), Box::new(rs)); }
                            a.wrapping_div(*b)
                        }
                        BinExpr::Mod => {
                            if *b == 0 { return Expr::BinOp(*op, Box::new(ls), Box::new(rs)); }
                            a.wrapping_rem(*b)
                        }
                    }),
                    _ => Expr::BinOp(*op, Box::new(ls), Box::new(rs)),
                }
            }
            Expr::Neg(e) => {
                let es = e.simplify();
                match &es {
                    Expr::Const(n) => Expr::Const(-n),
                    _ => Expr::Neg(Box::new(es)),
                }
            }
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Const(n) => write!(f, "{}", n),
            Expr::Var(n) => write!(f, "{}", n),
            Expr::BinOp(op, l, r) => {
                let op_str = match op {
                    BinExpr::Add => "+",
                    BinExpr::Sub => "-",
                    BinExpr::Mul => "×",
                    BinExpr::Div => "/",
                    BinExpr::Mod => "%",
                };
                write!(f, "({} {} {})", l, op_str, r)
            }
            Expr::Neg(e) => write!(f, "(-{})", e),
        }
    }
}

/// A Boolean assertion (logical formula).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Assert {
    /// Boolean constant.
    Bool(bool),
    /// Equality: expr = expr.
    Eq(Expr, Expr),
    /// Inequality: expr ≠ expr.
    Neq(Expr, Expr),
    /// Less than.
    Lt(Expr, Expr),
    /// Less than or equal.
    Le(Expr, Expr),
    /// Greater than.
    Gt(Expr, Expr),
    /// Greater than or equal.
    Ge(Expr, Expr),
    /// Conjunction.
    And(Box<Assert>, Box<Assert>),
    /// Disjunction.
    Or(Box<Assert>, Box<Assert>),
    /// Implication.
    Implies(Box<Assert>, Box<Assert>),
    /// Negation.
    Not(Box<Assert>),
    /// Forall.
    Forall(String, Box<Assert>),
    /// Exists.
    Exists(String, Box<Assert>),
}

impl Assert {
    /// Boolean constant true.
    pub fn tt() -> Self {
        Assert::Bool(true)
    }

    /// Boolean constant false.
    pub fn ff() -> Self {
        Assert::Bool(false)
    }

    /// Equality assertion.
    pub fn eq(l: Expr, r: Expr) -> Self {
        Assert::Eq(l, r)
    }

    /// Inequality.
    pub fn neq(l: Expr, r: Expr) -> Self {
        Assert::Neq(l, r)
    }

    /// Less than.
    pub fn lt(name: &str, val: i64) -> Self {
        Assert::Lt(Expr::var(name), Expr::const_val(val))
    }

    /// Less than or equal.
    pub fn le(name: &str, val: i64) -> Self {
        Assert::Le(Expr::var(name), Expr::const_val(val))
    }

    /// Greater than (convenience for variable > constant).
    pub fn gt(name: &str, val: i64) -> Self {
        Assert::Gt(Expr::var(name), Expr::const_val(val))
    }

    /// Greater than (full expression version, same as gt).
    pub fn gt_expr(name: &str, val: i64) -> Self {
        Assert::Gt(Expr::var(name), Expr::const_val(val))
    }

    /// Greater than or equal.
    pub fn ge(name: &str, val: i64) -> Self {
        Assert::Ge(Expr::var(name), Expr::const_val(val))
    }

    /// Conjunction.
    pub fn and(l: Assert, r: Assert) -> Self {
        Assert::And(Box::new(l), Box::new(r))
    }

    /// Disjunction.
    pub fn or(l: Assert, r: Assert) -> Self {
        Assert::Or(Box::new(l), Box::new(r))
    }

    /// Implication.
    pub fn implies(l: Assert, r: Assert) -> Self {
        Assert::Implies(Box::new(l), Box::new(r))
    }

    /// Negation.
    pub fn not(a: Assert) -> Self {
        Assert::Not(Box::new(a))
    }

    /// Forall quantifier.
    pub fn forall(var: &str, body: Assert) -> Self {
        Assert::Forall(var.to_string(), Box::new(body))
    }

    /// Substitute variable `name` with expression `replacement`.
    pub fn substitute(&self, name: &str, replacement: &Expr) -> Assert {
        match self {
            Assert::Bool(_) => self.clone(),
            Assert::Eq(l, r) => Assert::Eq(
                l.substitute(name, replacement),
                r.substitute(name, replacement),
            ),
            Assert::Neq(l, r) => Assert::Neq(
                l.substitute(name, replacement),
                r.substitute(name, replacement),
            ),
            Assert::Lt(l, r) => Assert::Lt(
                l.substitute(name, replacement),
                r.substitute(name, replacement),
            ),
            Assert::Le(l, r) => Assert::Le(
                l.substitute(name, replacement),
                r.substitute(name, replacement),
            ),
            Assert::Gt(l, r) => Assert::Gt(
                l.substitute(name, replacement),
                r.substitute(name, replacement),
            ),
            Assert::Ge(l, r) => Assert::Ge(
                l.substitute(name, replacement),
                r.substitute(name, replacement),
            ),
            Assert::And(l, r) => Assert::and(
                l.substitute(name, replacement),
                r.substitute(name, replacement),
            ),
            Assert::Or(l, r) => Assert::or(
                l.substitute(name, replacement),
                r.substitute(name, replacement),
            ),
            Assert::Implies(l, r) => Assert::implies(
                l.substitute(name, replacement),
                r.substitute(name, replacement),
            ),
            Assert::Not(a) => Assert::not(a.substitute(name, replacement)),
            Assert::Forall(v, body) if v != name => {
                Assert::forall(v, body.substitute(name, replacement))
            }
            Assert::Forall(v, body) => Assert::forall(v, *body.clone()),
            Assert::Exists(v, body) if v != name => {
                Assert::exists(v, body.substitute(name, replacement))
            }
            Assert::Exists(v, body) => Assert::exists(v, *body.clone()),
        }
    }

    /// Exists quantifier.
    pub fn exists(var: &str, body: Assert) -> Self {
        Assert::Exists(var.to_string(), Box::new(body))
    }

    /// Evaluate the assertion given variable bindings.
    pub fn evaluate(&self, env: &std::collections::HashMap<String, i64>) -> Option<bool> {
        match self {
            Assert::Bool(b) => Some(*b),
            Assert::Eq(l, r) => Some(l.evaluate(env)? == r.evaluate(env)?),
            Assert::Neq(l, r) => Some(l.evaluate(env)? != r.evaluate(env)?),
            Assert::Lt(l, r) => Some(l.evaluate(env)? < r.evaluate(env)?),
            Assert::Le(l, r) => Some(l.evaluate(env)? <= r.evaluate(env)?),
            Assert::Gt(l, r) => Some(l.evaluate(env)? > r.evaluate(env)?),
            Assert::Ge(l, r) => Some(l.evaluate(env)? >= r.evaluate(env)?),
            Assert::And(l, r) => Some(l.evaluate(env)? && r.evaluate(env)?),
            Assert::Or(l, r) => Some(l.evaluate(env)? || r.evaluate(env)?),
            Assert::Implies(l, r) => Some(!l.evaluate(env)? || r.evaluate(env)?),
            Assert::Not(a) => Some(!a.evaluate(env)?),
            Assert::Forall(_, _) | Assert::Exists(_, _) => None, // Quantifiers need more context
        }
    }

    /// Simplify the assertion by simplifying sub-expressions.
    pub fn simplify(&self) -> Assert {
        match self {
            Assert::Bool(_) => self.clone(),
            Assert::Eq(l, r) => Assert::eq(l.simplify(), r.simplify()),
            Assert::Neq(l, r) => Assert::neq(l.simplify(), r.simplify()),
            Assert::Lt(l, r) => Assert::Lt(l.simplify(), r.simplify()),
            Assert::Le(l, r) => Assert::Le(l.simplify(), r.simplify()),
            Assert::Gt(l, r) => Assert::Gt(l.simplify(), r.simplify()),
            Assert::Ge(l, r) => Assert::Ge(l.simplify(), r.simplify()),
            Assert::And(l, r) => Assert::and(l.simplify(), r.simplify()),
            Assert::Or(l, r) => Assert::or(l.simplify(), r.simplify()),
            Assert::Implies(l, r) => Assert::implies(l.simplify(), r.simplify()),
            Assert::Not(a) => Assert::not(a.simplify()),
            Assert::Forall(v, b) => Assert::forall(v, b.simplify()),
            Assert::Exists(v, b) => Assert::exists(v, b.simplify()),
        }
    }
}

impl fmt::Display for Assert {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Assert::Bool(true) => write!(f, "true"),
            Assert::Bool(false) => write!(f, "false"),
            Assert::Eq(l, r) => write!(f, "({} = {})", l, r),
            Assert::Neq(l, r) => write!(f, "({} ≠ {})", l, r),
            Assert::Lt(l, r) => write!(f, "({} < {})", l, r),
            Assert::Le(l, r) => write!(f, "({} ≤ {})", l, r),
            Assert::Gt(l, r) => write!(f, "({} > {})", l, r),
            Assert::Ge(l, r) => write!(f, "({} ≥ {})", l, r),
            Assert::And(l, r) => write!(f, "({} ∧ {})", l, r),
            Assert::Or(l, r) => write!(f, "({} ∨ {})", l, r),
            Assert::Implies(l, r) => write!(f, "({} → {})", l, r),
            Assert::Not(a) => write!(f, "¬{}", a),
            Assert::Forall(v, b) => write!(f, "(∀{}. {})", v, b),
            Assert::Exists(v, b) => write!(f, "(∃{}. {})", v, b),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr_const() {
        let e = Expr::const_val(42);
        assert_eq!(format!("{}", e), "42");
    }

    #[test]
    fn test_expr_var() {
        let e = Expr::var("x");
        assert_eq!(format!("{}", e), "x");
        assert_eq!(e.variables(), vec!["x"]);
    }

    #[test]
    fn test_expr_substitute() {
        let e = Expr::add(Expr::var("x"), Expr::const_val(1));
        let sub = e.substitute("x", &Expr::const_val(5));
        assert_eq!(sub, Expr::add(Expr::const_val(5), Expr::const_val(1)));
    }

    #[test]
    fn test_expr_evaluate() {
        let mut env = std::collections::HashMap::new();
        env.insert("x".to_string(), 5);
        let e = Expr::add(Expr::var("x"), Expr::const_val(3));
        assert_eq!(e.evaluate(&env), Some(8));
    }

    #[test]
    fn test_expr_simplify() {
        let e = Expr::add(Expr::const_val(2), Expr::const_val(3));
        assert_eq!(e.simplify(), Expr::const_val(5));
    }

    #[test]
    fn test_assert_eq() {
        let a = Assert::eq(Expr::var("x"), Expr::const_val(5));
        assert_eq!(format!("{}", a), "(x = 5)");
    }

    #[test]
    fn test_assert_substitute() {
        let a = Assert::Gt(Expr::var("x"), Expr::const_val(0));
        let sub = a.substitute("x", &Expr::add(Expr::var("x"), Expr::const_val(1)));
        // After substitution: x+1 > 0
        let mut env = std::collections::HashMap::new();
        env.insert("x".to_string(), 0);
        assert_eq!(sub.evaluate(&env), Some(true));
    }

    #[test]
    fn test_assert_evaluate() {
        let a = Assert::and(
            Assert::Gt(Expr::var("x"), Expr::const_val(0)),
            Assert::Lt(Expr::var("x"), Expr::const_val(10)),
        );
        let mut env = std::collections::HashMap::new();
        env.insert("x".to_string(), 5);
        assert_eq!(a.evaluate(&env), Some(true));
        env.insert("x".to_string(), 15);
        assert_eq!(a.evaluate(&env), Some(false));
    }

    #[test]
    fn test_assert_implies() {
        let a = Assert::implies(
            Assert::Gt(Expr::var("x"), Expr::const_val(0)),
            Assert::Gt(Expr::var("x"), Expr::const_val(0)),
        );
        let mut env = std::collections::HashMap::new();
        env.insert("x".to_string(), 5);
        assert_eq!(a.evaluate(&env), Some(true));
    }

    #[test]
    fn test_quantifiers() {
        let a = Assert::forall("x", Assert::Gt(Expr::var("x"), Expr::const_val(0)));
        assert!(format!("{}", a).contains("∀"));
        let e = Assert::exists("x", Assert::Gt(Expr::var("x"), Expr::const_val(0)));
        assert!(format!("{}", e).contains("∃"));
    }
}
