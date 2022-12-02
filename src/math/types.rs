
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeHierarchyNode {
    contents: CompoundType,
    children: Vec<TypeHierarchyNode>,
}

impl From<CompoundType> for TypeHierarchyNode {
    fn from(val: CompoundType) -> Self {
        TypeHierarchyNode::singleton(val)
    }
}

impl From<SimpleType> for TypeHierarchyNode {
    fn from(val: SimpleType) -> Self {
        TypeHierarchyNode::singleton(val)
    }
}

impl From<&str> for TypeHierarchyNode {
    fn from(val: &str) -> Self {
        TypeHierarchyNode::singleton(Into::<CompoundType>::into(val))
    }
}

impl TypeHierarchyNode {

    pub fn new(contents: impl Into<CompoundType>, children: Vec<impl Into<TypeHierarchyNode>>) -> TypeHierarchyNode {
        TypeHierarchyNode {
            contents: contents.into(),
            children: children.into_iter().map(|child| child.into()).collect(),
        }
    }

    pub fn singleton(contents: impl Into<CompoundType>) -> TypeHierarchyNode {
        TypeHierarchyNode {
            contents: contents.into(),
            children: Vec::new(),
        }
    }

    pub fn get_contents(&self) -> &CompoundType {
        &self.contents
    }

    pub fn get_children(&self) -> &Vec<TypeHierarchyNode> {
        &self.children
    }

    pub fn n_children(&self) -> usize {
        self.children.len()
    }

    pub fn from_vec(types: Vec<impl Into<CompoundType> + Clone>) -> TypeHierarchyNode {
        if types.len() == 1 {
            TypeHierarchyNode::singleton(types[0].clone().into())
        } else {
            let mut children = Vec::new();
            let child = TypeHierarchyNode::from_vec(types[1..].to_vec());
            children.push(child);
            TypeHierarchyNode::new(types[0].clone().into(), children)
        }
    }

    pub fn subtype(&self, lhs: impl Into<CompoundType> + Clone, rhs: impl Into<CompoundType> + Clone) -> bool {
        let lhs = lhs.into();
        let rhs = rhs.into();
        if lhs == rhs {
            return false;
        }
        self.subtype_eq(lhs, rhs)
    }

    pub fn subtype_eq(&self, lhs: impl Into<CompoundType> + Clone, rhs: impl Into<CompoundType> + Clone) -> bool {
        let lhs = lhs.into();
        let rhs = rhs.into();
        if lhs == rhs {
            true
        } else if rhs == self.contents {
            self.children.iter().any(|child| child.contains(lhs.clone()))
        } else {
            self.children.iter().any(|child| child.subtype_eq(lhs.clone(), rhs.clone()))
        }
    }

    pub fn contains(&self, contents: impl Into<CompoundType> + Clone) -> bool {
        let contents = contents.into();
        if contents == self.contents {
            true
        } else {
            self.children.iter().any(|child| child.contains(contents.clone()))
        }
    }

}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompoundType {
    types: Vec<SimpleType>,
}

impl From<SimpleType> for CompoundType {
    fn from(simple_type: SimpleType) -> Self {
        Self::simple(simple_type)
    }
}

impl From<&str> for CompoundType {

    fn from(simple_type: &str) -> Self {
        Self::simple(simple_type)
    }

}

impl CompoundType {
    pub fn new(types: Vec<SimpleType>) -> Self {
        CompoundType { types }
    }

    pub fn simple(simple_type: impl Into<SimpleType>) -> Self {
        CompoundType {
            types: vec![simple_type.into()],
        }
    }
    pub fn get_types(&self) -> &Vec<SimpleType> {
        &self.types
    }

}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SimpleType {
    Object,
    Custom(String),
}

impl From<&str> for SimpleType {

    fn from(simple_type: &str) -> Self {
        Self::Custom(simple_type.to_string())
    }

}

impl SimpleType {

    pub fn new(name: &str) -> SimpleType {
        SimpleType::Custom(name.to_string())
    }

}

#[cfg(test)]
mod test_types {
    use super::*;

    #[test]
    fn test_type_hierarchy_node_from_vec() {
        
        let hierarchy = TypeHierarchyNode::from_vec(
            vec![
                SimpleType::Object,
                SimpleType::new("Complex"),
                SimpleType::new("Real"),
                SimpleType::new("Rational"),
                SimpleType::new("Integer"),
            ]
        );

        assert!(!hierarchy.subtype(SimpleType::Object, SimpleType::Object));
        assert!(hierarchy.subtype_eq(SimpleType::Object, SimpleType::Object));

        assert!(hierarchy.subtype(SimpleType::new("Complex"), SimpleType::Object));
        assert!(hierarchy.subtype_eq(SimpleType::new("Complex"), SimpleType::Object));
    
        assert!(hierarchy.subtype(SimpleType::new("Real"), SimpleType::Object));
        assert!(hierarchy.subtype_eq(SimpleType::new("Real"), SimpleType::Object));

        assert!(hierarchy.subtype(SimpleType::new("Rational"), SimpleType::Object));
        assert!(hierarchy.subtype_eq(SimpleType::new("Rational"), SimpleType::Object));

        assert!(hierarchy.subtype(SimpleType::new("Integer"), SimpleType::Object));
        assert!(hierarchy.subtype_eq(SimpleType::new("Integer"), SimpleType::Object));

        assert!(hierarchy.subtype(SimpleType::new("Real"), SimpleType::new("Complex")));
        assert!(hierarchy.subtype_eq(SimpleType::new("Real"), SimpleType::new("Complex")));

        assert!(hierarchy.subtype(SimpleType::new("Rational"), SimpleType::new("Complex")));
        assert!(hierarchy.subtype_eq(SimpleType::new("Rational"), SimpleType::new("Complex")));

        assert!(!hierarchy.subtype(SimpleType::new("Complex"), SimpleType::new("Real")));
        assert!(!hierarchy.subtype_eq(SimpleType::new("Complex"), SimpleType::new("Real")));

        assert!(hierarchy.subtype(SimpleType::new("Rational"), SimpleType::new("Real")));
        assert!(hierarchy.subtype_eq(SimpleType::new("Rational"), SimpleType::new("Real")));
    }

    #[test]
    fn test_hierarchy_node_can_determine_subtypes() {
        let hierarchy = TypeHierarchyNode::new(
            SimpleType::Object,
            vec![
                TypeHierarchyNode::new(
                    SimpleType::new("Rational"),
                    vec![
                        SimpleType::new("Integer"),
                    ],
                ),
                TypeHierarchyNode::singleton(
                    SimpleType::new("Irrational"),
                )
            ]
        );

        assert!(hierarchy.subtype(SimpleType::new("Rational"), SimpleType::Object));
        assert!(hierarchy.subtype(SimpleType::new("Integer"), SimpleType::Object));
        assert!(hierarchy.subtype(SimpleType::new("Irrational"), SimpleType::Object));

        assert!(hierarchy.subtype(SimpleType::new("Integer"), SimpleType::new("Rational")));
        
        assert!(!hierarchy.subtype(SimpleType::new("Integer"), SimpleType::new("Irrational")));

        assert!(!hierarchy.subtype(SimpleType::new("Rational"), SimpleType::new("Integer")));
        assert!(!hierarchy.subtype(SimpleType::new("Irrational"), SimpleType::new("Integer")));
        assert!(!hierarchy.subtype(SimpleType::Object, SimpleType::new("Integer")));

    }
}