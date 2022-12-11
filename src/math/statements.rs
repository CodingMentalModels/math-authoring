use std::{collections::{HashMap, HashSet}, fmt::{Display, Formatter, self}, error::Error, iter};
use itertools::Itertools;

use crate::math::types::{CompoundType};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Transformation {
    from: Statement,
    to: Statement,
}

impl Transformation {

    pub fn new(from: Statement, to: Statement) -> Transformation {
        Transformation { from, to }
    }

    pub fn get_from(&self) -> &Statement {
        &self.from
    }

    pub fn get_to(&self) -> &Statement {
        &self.to
    }

    pub fn transform_strict(&self, statement: &Statement) -> Result<Statement, String> {
        if statement == &self.from {
            Ok(self.to.clone())
        } else {
            Err(format!("Cannot transform statement: {} != {}", statement, self.from))
        }
    }

    pub fn transform(&self, statement: &Statement, mapping: &HashMap<Symbol, Symbol>) -> Result<Statement, String> {
        let mapped_transform = self.substitute_all(mapping)?;
        mapped_transform.transform_strict(statement)
    }

    pub fn substitute_all(&self, mapping: &HashMap<Symbol, Symbol>) -> Result<Transformation, String> {
        Ok(Transformation::new(self.from.substitute_all(mapping)?, self.to.substitute_all(mapping)?))
    }

}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Statement {
    quantifiers: Vec<Quantifier>,
    subject: SymbolNode,
}

impl Display for Statement {
    
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            write!(f, "{} {}", self.quantifiers.iter().map(|q| format!("{}", q)).collect::<Vec<_>>().join(" "), self.subject)
        }
}

impl Statement {

    pub fn new(quantifiers: Vec<Quantifier>, subject: impl Into<SymbolNode>) -> Statement {
        Statement { quantifiers, subject: subject.into() }
    }

    pub fn substitute(&self, from_symbol: &Symbol, to_symbol: &Symbol) -> Result<Statement, String> {
        Ok(Statement::new(Quantifier::substitute_several(&self.quantifiers, from_symbol, to_symbol), self.subject.substitute(from_symbol, to_symbol)))
    }

    pub fn substitute_all(&self, mapping: &HashMap<Symbol, Symbol>) -> Result<Statement, String> {
        let quantifiers = Quantifier::substitute_several_all(&self.quantifiers, mapping)?;
        let subject = self.subject.clone().substitute_all(mapping);
        Ok(Statement::new(quantifiers, subject))
    }

    pub fn is_isomorphic(&self, other: &Self) -> bool {
        let bijections = Quantifier::get_isomorphisms(&self.quantifiers, &other.quantifiers);

        if bijections.len() == 0 {
            return false;
        }

        bijections.into_iter().any(|b| self.subject.is_isomorphic_under(&other.subject, &b))
    }
}


#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Quantifier {
    All(Symbol, CompoundType),
    Exists(Symbol, CompoundType),
    NotAll(Symbol, CompoundType),
    NotExists(Symbol, CompoundType),
}

impl Display for Quantifier {

    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Quantifier::All(symbol, compound_type) => write!(f, "∀{}:{}", symbol, compound_type),
            Quantifier::Exists(symbol, compound_type) => write!(f, "∃{}:{}", symbol, compound_type),
            Quantifier::NotAll(symbol, compound_type) => write!(f, "¬∀{}:{}", symbol, compound_type),
            Quantifier::NotExists(symbol, compound_type) => write!(f, "¬∃{}:{}", symbol, compound_type),
        }
    }
}

impl Quantifier {

    pub fn get_symbol(&self) -> Symbol {
        match self {
            Quantifier::All(symbol, _) => symbol.clone(),
            Quantifier::Exists(symbol, _) => symbol.clone(),
            Quantifier::NotAll(symbol, _) => symbol.clone(),
            Quantifier::NotExists(symbol, _) => symbol.clone(),
        }
    }

    pub fn get_type(&self) -> CompoundType {
        match self {
            Quantifier::All(_, compound_type) => compound_type.clone(),
            Quantifier::Exists(_, compound_type) => compound_type.clone(),
            Quantifier::NotAll(_, compound_type) => compound_type.clone(),
            Quantifier::NotExists(_, compound_type) => compound_type.clone(),
        }
    }

    pub fn get_isomorphisms(lhs: &Vec<Self>, rhs: &Vec<Self>) -> Vec<HashMap<Symbol, Symbol>> {
        if lhs.len() != rhs.len() {
            return vec![];
        }
        
        Self::get_isomorphisms_internal(lhs.clone(), rhs.clone(), Vec::new()).unwrap_or_else(|_| vec![])
    }

    fn get_isomorphisms_internal(lhs: Vec<Self>, rhs: Vec<Self>, so_far: Vec<HashMap<Symbol, Symbol>>) -> Result<Vec<HashMap<Symbol, Symbol>>, String> {
        
        let mut thru_idx = 0;
        loop {
            if Self::has_same_quantifier(&lhs[thru_idx], &rhs[thru_idx]) {
                thru_idx += 1;
                if thru_idx == lhs.len() {
                    break;
                }
            } else {
                break;
            }
        }

        let mut lhs_thru = lhs[0..thru_idx].to_vec();
        let mut rhs_thru = rhs[0..thru_idx].to_vec();

        let lhs_by_type = Self::group_by_type(lhs_thru.to_vec());
        let rhs_by_type = Self::group_by_type(rhs_thru.to_vec());
        
        if lhs_by_type.keys().collect::<HashSet<_>>() != rhs_by_type.keys().collect::<HashSet<_>>() {
            return Err(format!("Quantifiers have different types: {:?} vs. {:?}", lhs_by_type.keys(), rhs_by_type.keys()));
        }

        let mut new_so_far = so_far.clone();
        for k in lhs_by_type.keys() {
            let lhs_quantifiers = lhs_by_type.get(k).unwrap();
            let rhs_quantifiers = rhs_by_type.get(k).unwrap();
            if lhs_quantifiers.len() != rhs_quantifiers.len() {
                return Err(format!("Quantifiers have different number of symbols of type {}: {:?} vs. {:?}", k, lhs_quantifiers, rhs_quantifiers));
            }
            let mut new_mappings: Vec<HashMap<Symbol, Symbol>> = Vec::new();
            if lhs_quantifiers.len() == 1 {
                let lhs_symbol = lhs_quantifiers[0].get_symbol();
                let rhs_symbol = rhs_quantifiers[0].get_symbol();
                new_mappings = vec![vec![(lhs_symbol, rhs_symbol)].into_iter().collect::<HashMap<_, _>>()];
            } else {
                if lhs_quantifiers[0].is_reorderable() {
                    let permutations = Self::get_symbol_permutations(rhs_quantifiers.clone());
                    let lhs_symbols = lhs_quantifiers.into_iter().map(|x| x.get_symbol()).collect();
                    let lhs_basis: Vec<Vec<Symbol>> = iter::repeat(lhs_symbols).take(permutations.len()).collect();
                    new_mappings = lhs_basis.into_iter().zip(permutations).map(|(l, r)| l.into_iter().zip(r).collect()).collect();
                } else {
                    return Err(format!("Quantifiers are not reorderable: {:?} vs. {:?}", lhs_quantifiers, rhs_quantifiers));
                }
            }
            if new_so_far.len() == 0 && new_mappings.len() > 0 {
                new_so_far.push(HashMap::new());
            }
            new_so_far = new_so_far.iter().map(
                |m| new_mappings.iter().map(
                    |mapping| {
                        let mut m_clone = m.clone();
                        m_clone.extend(mapping.clone());
                        return m_clone;
                    }
                ).collect::<Vec<HashMap<_, _>>>()
            ).flatten().collect();
        }
        return Ok(new_so_far);
    }

    fn group_by_type(quantifiers: Vec<Self>) -> HashMap<CompoundType, Vec<Self>> {
        let mut map = HashMap::new();
        for quantifier in quantifiers {
            let entry = map.entry(quantifier.get_type()).or_insert_with(|| vec![]);
            entry.push(quantifier);
        }
        map
    }

    fn has_same_quantifier(lhs: &Quantifier, rhs: &Quantifier) -> bool {
        match (lhs, rhs) {
            (Quantifier::All(_, _), Quantifier::All(_, _)) => true,
            (Quantifier::Exists(_, _), Quantifier::Exists(_, _)) => true,
            (Quantifier::NotAll(_, _), Quantifier::NotAll(_, _)) => true,
            (Quantifier::NotExists(_, _), Quantifier::NotExists(_, _)) => true,
            _ => false,
        }
    }

    fn is_reorderable(&self) -> bool {
        match self {
            Quantifier::All(_, _) => true,
            Quantifier::Exists(_, _) => false,
            Quantifier::NotAll(_, _) => false,
            Quantifier::NotExists(_, _) => true,
        }
    }

    fn get_symbol_permutations(quantifiers: Vec<Self>) -> Vec<Vec<Symbol>> {
        let quantifiers_length = quantifiers.len();
        quantifiers.into_iter().map(|x| x.get_symbol()).permutations(quantifiers_length).collect()
    }

    pub fn substitute(&self, from_symbol: &Symbol, to_symbol: &Symbol) -> Quantifier {
        if &self.get_symbol() != from_symbol {
            return self.clone();
        }
        match self {
            Quantifier::All(_, compound_type) => Quantifier::All(to_symbol.clone(), compound_type.clone()),
            Quantifier::Exists(_, compound_type) => Quantifier::Exists(to_symbol.clone(), compound_type.clone()),
            Quantifier::NotAll(_, compound_type) => Quantifier::NotAll(to_symbol.clone(), compound_type.clone()),
            Quantifier::NotExists(_, compound_type) => Quantifier::NotExists(to_symbol.clone(), compound_type.clone()),
        }
    }

    fn substitute_several(quantifiers: &Vec<Self>, from_symbol: &Symbol, to_symbol: &Symbol) -> Vec<Self> {
        quantifiers.iter().map(|quantifier| quantifier.substitute(from_symbol, to_symbol)).collect()
    }

    pub fn substitute_several_all(quantifiers: &Vec<Self>, mapping: &HashMap<Symbol, Symbol>) -> Result<Vec<Self>, String> {
        let mut new_quantifiers = quantifiers.clone();
        for (from_symbol, to_symbol) in mapping {
            new_quantifiers = Quantifier::reconcile(Quantifier::substitute_several(&new_quantifiers, &from_symbol, &to_symbol))?;
        }
        Ok(new_quantifiers)
    }

    fn reconcile(quantifiers: Vec<Self>) -> Result<Vec<Self>, String> {
        let mut offset_quantifiers: Vec<Option<Quantifier>> = quantifiers.clone().into_iter().map(|x| Some(x)).skip(1).collect();
        offset_quantifiers.push(None);
        let to_return: Result<Vec<Quantifier>, String> = quantifiers.into_iter().zip(offset_quantifiers).filter_map(|(first, second)| {
            if second.is_none() {
                return Some(Ok(first));
            }
            let second = second.unwrap();
            if first.get_symbol() == second.get_symbol() {
                if first.get_type() != second.get_type() {
                    return Some(Err(format!("Quantifiers can't be reconciled as they have different types: {:?} and {:?}", first, second)));
                }
                match (&first, &second) {
                    (Quantifier::All(_, _), Quantifier::All(_, _)) => None,
                    (Quantifier::NotExists(_, _), Quantifier::NotExists(_, _)) => None,
                    (_, _) => Some(Err(format!("Quantifiers can't be reconciled as they aren't universal: {:?} and {:?}", first, second))),
                }
            } else {
                Some(Ok(first))
            }
        }).collect();
        let to_return = to_return?;
        if Self::is_duplicative(&to_return) {
            return Err(format!("Quantifiers can't be reconciled as they aren't adjacent: {:?}", to_return));
        }
        Ok(to_return)
    }

    pub fn is_duplicative(quantifiers: &Vec<Self>) -> bool {
        quantifiers.iter().collect::<HashSet<_>>().len() != quantifiers.len()
    }

}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct SymbolNode {
    symbol: Symbol,
    children: Vec<SymbolNode>,
}

impl Display for SymbolNode {
    
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.symbol);
            if !self.children.is_empty() {
                write!(f, "(")?;
                for (i, child) in self.children.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", child)?;
                }
                write!(f, ")")?;
            }
            Ok(())
        }
}

impl From<Symbol> for SymbolNode {
    fn from(symbol: Symbol) -> Self {
        SymbolNode::singleton(symbol)
    }
}

impl From<&str> for SymbolNode {
    fn from(symbol: &str) -> Self {
        SymbolNode::singleton(symbol)
    }
}

impl SymbolNode {

    pub fn new(symbol: impl Into<Symbol>, children: Vec<impl Into<SymbolNode>>) -> SymbolNode {
        SymbolNode { symbol: symbol.into(), children: children.into_iter().map(|child| child.into()).collect() }
    }

    pub fn singleton(symbol: impl Into<Symbol>) -> SymbolNode {
        SymbolNode::new(symbol.into(), Vec::<SymbolNode>::new())
    }

    pub fn unary(symbol: impl Into<Symbol>, child: impl Into<SymbolNode>) -> SymbolNode {
        SymbolNode::new(symbol.into(), vec![child])
    }

    pub fn binary(symbol: impl Into<Symbol>, left: impl Into<SymbolNode>, right: impl Into<SymbolNode>) -> SymbolNode {
        SymbolNode::new(symbol.into(), vec![left.into(), right.into()])
    }

    pub fn ternary(symbol: impl Into<Symbol>, left: impl Into<SymbolNode>, middle: impl Into<SymbolNode>, right: impl Into<SymbolNode>) -> SymbolNode {
        SymbolNode::new(symbol.into(), vec![left.into(), middle.into(), right.into()])
    }

    pub fn get_isomorphisms(&self, other: &SymbolNode, potential_bijections: &Vec<HashMap<Symbol, Symbol>>) -> Vec<HashMap<Symbol, Symbol>> {
        potential_bijections.iter().filter(|bijection| self.is_isomorphic_under(other, bijection)).map(|bijection| bijection.clone()).collect()
    }

    pub fn is_isomorphic_under(&self, other: &SymbolNode, bijection: &HashMap<Symbol, Symbol>) -> bool {
        self.substitute_all(bijection) == *other
    }

    pub fn substitute(&self, from_symbol: &Symbol, to_symbol: &Symbol) -> SymbolNode {
        let contents = if self.symbol == *from_symbol {
            to_symbol.clone()
        } else {
            self.symbol.clone()
        };
        SymbolNode::new(contents, self.children.iter().map(|child| child.substitute(from_symbol, to_symbol)).collect())
    }

    pub fn substitute_all(&self, substitutions: &HashMap<Symbol, Symbol>) -> Self {
        let from_to_unambiguous: HashMap<Symbol, Symbol> = substitutions.iter().enumerate().map(|(i, (from, to))| (from.clone(), Symbol::new(&i.to_string()))).collect();
        let to_to_unambiguous: HashMap<Symbol, Symbol> = substitutions.iter().enumerate().map(|(i, (from, to))| (Symbol::new(&i.to_string()), to.clone())).collect();

        let unambiguous = self.substitute_all_unchecked(&from_to_unambiguous);
        unambiguous.substitute_all_unchecked(&to_to_unambiguous)
    }

    fn substitute_all_unchecked(&self, substitutions: &HashMap<Symbol, Symbol>) -> Self {
        let mut to_return = self.clone();
        for (from, to) in substitutions {
            to_return = to_return.substitute(&from, &to);
        }
        return to_return;
    }

}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Symbol {
    name: String,
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl From<&str> for Symbol {
    fn from(name: &str) -> Self {
        Symbol::new(name)
    }
}

impl Symbol {

    pub fn new(name: &str) -> Symbol {
        Symbol { name: name.to_string() }
    }
}

#[cfg(test)]
mod test_statement {
    use crate::math::types::SimpleType;

    use super::*;

    #[test]
    fn test_statement_transforms_strictly() {
        
        let statement = Statement::new(
            vec![
                Quantifier::Exists(Symbol::new("="), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                Quantifier::All(Symbol::new("x"), SimpleType::Object.into()),
                Quantifier::All(Symbol::new("y"), SimpleType::Object.into())],
            SymbolNode::binary(
                "=",
                "x",
                "y",
            )
        );

        let x_equals_y = Statement::new(
            vec![
                Quantifier::Exists("=".into(), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                Quantifier::All("x".into(), SimpleType::Object.into()),
                Quantifier::All("y".into(), SimpleType::Object.into()),
            ],
            SymbolNode::new(
                Symbol::new("="),
                vec![
                    Into::<SymbolNode>::into("x"),
                    Into::<SymbolNode>::into("y"),
                ],
            ),
        );
        let x_equals_z = x_equals_y.substitute(&"y".into(), &"z".into()).unwrap();

        let transformation = Transformation::new(
            x_equals_y.clone(),
            x_equals_z.clone(),
        );

        assert_eq!(statement, x_equals_y);
        
        let transformed = transformation.transform_strict(&statement).unwrap();
        
        assert_eq!(transformed, x_equals_z);

    }

    #[test]
    fn test_statement_transforms() {
        
        let statement = Statement::new(
            vec![
                Quantifier::Exists(Symbol::new("="), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                Quantifier::All(Symbol::new("a"), SimpleType::Object.into()),
                Quantifier::All(Symbol::new("b"), SimpleType::Object.into()),
                ],
            SymbolNode::binary(
                "=",
                "a",
                "b",
            )
        );

        let transformation = Transformation::new(
            Statement::new(
                vec![
                    Quantifier::Exists("=".into(), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                    Quantifier::All("x".into(), SimpleType::Object.into()),
                    Quantifier::All("y".into(), SimpleType::Object.into()),
                ],
                SymbolNode::new(
                    Symbol::new("="),
                    vec![
                        Into::<SymbolNode>::into("x"),
                        Into::<SymbolNode>::into("y"),
                    ],
                ),
            ),
            Statement::new(
                vec![
                    Quantifier::Exists("=".into(), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                    Quantifier::All("x".into(), SimpleType::Object.into()),
                ],
                SymbolNode::new(
                    Symbol::new("="),
                    vec![
                        Into::<SymbolNode>::into("x"),
                        Into::<SymbolNode>::into("x"),
                    ],
                ),
            ),
        );

        let transformed = transformation.transform(
            &statement,
            &vec![("x".into(), "a".into()), ("y".into(), "b".into())].into_iter().collect()
        ).unwrap();
        
        let expected = Statement::new(
            vec![
                Quantifier::Exists("=".into(), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                Quantifier::All("a".into(), SimpleType::Object.into()),
            ],
            SymbolNode::new(
                Symbol::new("="),
                vec![
                    Into::<SymbolNode>::into("a"),
                    Into::<SymbolNode>::into("a"),
                ],
            ),
        );

        assert_eq!(transformed, expected, "transformed != statement: {} != {}", transformed, statement);

    }

    #[test]
    fn test_statement_is_isomorphic() {
        
        let statement = Statement::new(
            vec![
                Quantifier::Exists(Symbol::new("="), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                Quantifier::All(Symbol::new("x"), SimpleType::Object.into()),
                Quantifier::All(Symbol::new("y"), SimpleType::Object.into()),
            ],
            SymbolNode::binary(
                "=",
                "x",
                "y",
            )
        );

        assert!(statement.is_isomorphic(&statement));

        let statement2 = Statement::new(
            vec![
                Quantifier::Exists(Symbol::new("="), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                Quantifier::All(Symbol::new("a"), SimpleType::Object.into()),
                Quantifier::All(Symbol::new("b"), SimpleType::Object.into()),
            ],
            SymbolNode::binary(
                "=",
                "a",
                "b",
            )
        );

        assert!(statement.is_isomorphic(&statement2));

        let different_by_symbol = Statement::new(
            vec![
                Quantifier::Exists(Symbol::new("="), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                Quantifier::All(Symbol::new("a"), SimpleType::Object.into()),
                Quantifier::All(Symbol::new("b"), SimpleType::Object.into()),
            ],
            SymbolNode::binary(
                "=",
                "a",
                "a",
            )
        );

        assert!(!statement.is_isomorphic(&different_by_symbol));

        let different_by_quantifier = Statement::new(
            vec![
                Quantifier::Exists(Symbol::new("="), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                Quantifier::Exists(Symbol::new("a"), SimpleType::Object.into()),
                Quantifier::All(Symbol::new("b"), SimpleType::Object.into()),
            ],
            SymbolNode::binary(
                "=",
                "a",
                "b",
            )
        );

        assert!(!statement.is_isomorphic(&different_by_quantifier));

        let different_by_type = Statement::new(
            vec![
                Quantifier::Exists(Symbol::new("="), CompoundType::new(vec![SimpleType::Object, SimpleType::Object, SimpleType::Object])),
                Quantifier::All(Symbol::new("a"), SimpleType::Object.into()),
                Quantifier::All(Symbol::new("b"), SimpleType::Object.into()),
            ],
            SymbolNode::binary(
                "=",
                "a",
                "b",
            )
        );

        assert!(!statement.is_isomorphic(&different_by_type));
        
    }

    #[test]
    fn test_statement_substitutes() {
        
        let statement = Statement::new(
            vec![
                Quantifier::Exists("=".into(), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                Quantifier::All("x".into(), SimpleType::Object.into()),
                Quantifier::All("y".into(), SimpleType::Object.into()),
            ],
            SymbolNode::new(
                Symbol::new("="),
                vec![
                    Into::<SymbolNode>::into("x"),
                    Into::<SymbolNode>::into("y"),
                ],
            ),
        );

        let x_to_a = statement.substitute(&"x".into(), &"a".into()).unwrap();

        let expected = Statement::new(
            vec![
                Quantifier::Exists("=".into(), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                Quantifier::All("a".into(), SimpleType::Object.into()),
                Quantifier::All("y".into(), SimpleType::Object.into()),
            ],
            SymbolNode::new(
                Symbol::new("="),
                vec![
                    Into::<SymbolNode>::into("a"),
                    Into::<SymbolNode>::into("y"),
                ],
            ),
        );

        assert_eq!(x_to_a, expected, "{} != {}", x_to_a, expected);

        let x_and_y_to_a = statement.substitute_all(
            &vec![
                ("x".into(), "a".into()),
                ("y".into(), "a".into()),
            ].into_iter().collect()
        ).unwrap();

        let expected = Statement::new(
            vec![
                Quantifier::Exists("=".into(), CompoundType::new(vec![SimpleType::Object, SimpleType::Object])),
                Quantifier::All("a".into(), SimpleType::Object.into()),
            ],
            SymbolNode::new(
                Symbol::new("="),
                vec![
                    Into::<SymbolNode>::into("a"),
                    Into::<SymbolNode>::into("a"),
                ],
            ),
        );

        assert_eq!(x_and_y_to_a, expected, "{} != {}", x_and_y_to_a, expected);

    }

    #[test]
    fn test_quantifier_substitutes() {
        
        let quantifier = Quantifier::All("x".into(), SimpleType::Object.into());
        assert_eq!(quantifier.substitute(&Symbol::from("x"), &Symbol::from("a")), Quantifier::All("a".into(), SimpleType::Object.into()));
    
        let quantifiers = vec![
            Quantifier::All("x".into(), SimpleType::Object.into()),
            Quantifier::All("y".into(), SimpleType::Object.into()),
            Quantifier::All("z".into(), SimpleType::Object.into()),
        ];
        assert_eq!(Quantifier::substitute_several_all(&quantifiers, 
            &vec![
                ("x".into(), "a".into()),
                ("y".into(), "b".into()),
                ("z".into(), "c".into()),
            ].into_iter().collect(),
        ).unwrap(),
            vec![
                Quantifier::All("a".into(), SimpleType::Object.into()),
                Quantifier::All("b".into(), SimpleType::Object.into()),
                Quantifier::All("c".into(), SimpleType::Object.into()),
            ]
        );
    }
    
    #[test]
    fn test_symbol_tree_substitutes() {
        
        let symbol_tree = SymbolNode::ternary("+", "a", "b", "c");
        assert_eq!(symbol_tree.substitute(&"b".into(), &"d".into()), SymbolNode::ternary("+", "a", "d", "c"));
        assert_eq!(symbol_tree.substitute(&"c".into(), &"d".into()), SymbolNode::ternary("+", "a", "b", "d"));
        assert_eq!(symbol_tree.substitute(&"a".into(), &"d".into()), SymbolNode::ternary("+", "d", "b", "c"));

        assert_eq!(
            symbol_tree.substitute_all_unchecked(&vec![
                ("a".into(), "d".into()),
                ("b".into(), "e".into()),
                ("c".into(), "f".into()),
            ].into_iter().collect()),
            SymbolNode::ternary("+", "d", "e", "f")
        );
        assert_eq!(
            symbol_tree.substitute_all(
                &vec![("a".into(), "d".into()), ("b".into(), "e".into()), ("c".into(), "f".into())].into_iter().collect()
            ),
            SymbolNode::ternary("+", "d", "e", "f")
        );

        assert_eq!(
            symbol_tree.substitute_all(
                &vec![("a".into(), "d".into()), ("b".into(), "d".into()), ("c".into(), "d".into())].into_iter().collect()
            ),
            SymbolNode::ternary("+", "d", "d", "d")
        );

        
        assert_eq!(
            symbol_tree.substitute_all(
                &vec![("a".into(), "d".into()), ("b".into(), "d".into())].into_iter().collect()
            ),
            SymbolNode::ternary("+", "d", "d", "c")
        );

        assert_eq!(
            symbol_tree.substitute_all(
                &vec![("a".into(), "b".into()), ("b".into(), "c".into())].into_iter().collect()
            ),
            SymbolNode::ternary("+", "b", "c", "c")
        );

        assert_eq!(
            SymbolNode::ternary("+", "2", "2", "4").substitute_all(
                &vec![("2".into(), "4".into()), ("4".into(), "2".into())].into_iter().collect()
            ),
            SymbolNode::ternary("+", "4", "4", "2")
        )
    }

    #[test]
    fn test_quantifier_is_isomorphic() {

        let single_quantifier = vec![
            Quantifier::All("x".into(), SimpleType::Object.into()),
        ];
        
        let bijections = Quantifier::get_isomorphisms(&single_quantifier, &single_quantifier);
        assert_eq!(bijections.len(), 1);
        assert_eq!(bijections[0], vec![("x".into(), "x".into())].into_iter().collect());

        let other_single_quantifier = vec![
            Quantifier::All("y".into(), SimpleType::Object.into()),
        ];
        let bijections = Quantifier::get_isomorphisms(&single_quantifier, &other_single_quantifier);
        assert_eq!(bijections.len(), 1);
        assert_eq!(bijections[0], vec![("x".into(), "y".into())].into_iter().collect());

        let wrong_type = vec![
            Quantifier::All("x".into(), "Number".into()),
        ];
        let bijections = Quantifier::get_isomorphisms(&single_quantifier, &wrong_type);
        assert_eq!(bijections.len(), 0);

        let wrong_quantifier = vec![
            Quantifier::Exists("x".into(), SimpleType::Object.into()),
        ];
        let bijections = Quantifier::get_isomorphisms(&single_quantifier, &wrong_quantifier);
        assert_eq!(bijections.len(), 0);

        let quantifiers = vec![
            Quantifier::All("x".into(), SimpleType::Object.into()),
            Quantifier::All("y".into(), SimpleType::Object.into()),
            Quantifier::All("z".into(), SimpleType::Object.into()),
        ];

        let bijections = Quantifier::get_isomorphisms(&quantifiers, &quantifiers);
        assert_eq!(bijections.len(), 6);

        let isomorphic = vec![
            Quantifier::All("a".into(), SimpleType::Object.into()),
            Quantifier::All("b".into(), SimpleType::Object.into()),
            Quantifier::All("c".into(), SimpleType::Object.into()),
        ];

        let bijections = Quantifier::get_isomorphisms(&quantifiers, &isomorphic);
        assert_eq!(bijections.len(), 6);

        let quantifiers = vec![
            Quantifier::All("x".into(), SimpleType::Object.into()),
            Quantifier::All("y".into(), SimpleType::Object.into()),
            Quantifier::All("z".into(), "Number".into()),
        ];

        let isomorphic = vec![
            Quantifier::All("a".into(), SimpleType::Object.into()),
            Quantifier::All("b".into(), SimpleType::Object.into()),
            Quantifier::All("c".into(), "Number".into()),
        ];

        let bijections = Quantifier::get_isomorphisms(&quantifiers, &isomorphic);
        assert_eq!(bijections.len(), 2);
    }

    #[test]
    fn test_quantifier_is_isomorphic_with_reconciliation() {
        
        let quantifiers = vec![
            Quantifier::All("x".into(), SimpleType::Object.into()),
            Quantifier::All("y".into(), "Number".into()),
            Quantifier::All("z".into(), SimpleType::Object.into()),
        ];

        let isomorphic = vec![
            Quantifier::All("a".into(), SimpleType::Object.into()),
            Quantifier::All("b".into(), SimpleType::Object.into()),
            Quantifier::All("c".into(), "Number".into()),
        ];

        let bijections = Quantifier::get_isomorphisms(&quantifiers, &isomorphic);
        assert_eq!(bijections.len(), 2);

        let quantifiers = vec![
            Quantifier::NotAll("x".into(), SimpleType::Object.into()),
            Quantifier::NotAll("y".into(), "Number".into()),
            Quantifier::NotAll("z".into(), SimpleType::Object.into()),
        ];

        let wrong_type = vec![
            Quantifier::NotAll("a".into(), SimpleType::Object.into()),
            Quantifier::NotAll("b".into(), SimpleType::Object.into()),
            Quantifier::NotAll("c".into(), "Number".into()),
        ];

        let bijections = Quantifier::get_isomorphisms(&quantifiers, &wrong_type);
        assert_eq!(bijections.len(), 0);

    }
}