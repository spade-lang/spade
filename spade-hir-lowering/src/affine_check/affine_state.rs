use std::{
    cell::RefCell,
    cmp::Ordering,
    collections::{BTreeSet, HashMap},
    rc::Rc,
};

use tracing::{info, trace};

use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, NameID},
};
use spade_hir::{Pattern, PatternKind, Expression};
use spade_types::ConcreteType;

use super::{error::Error, AffineCtx};

/// A witness for a type having a mut wire
#[derive(Debug, Clone)]
pub enum MutWireWitness {
    /// This type itself is a &mut
    This,
    /// This type has a field which is &mut or has its own &mut subfield
    Field(Identifier, Box<MutWireWitness>),
    /// This type has a tuple member which is &mut or has its own &mut subtuple
    TupleIndex(usize, Box<MutWireWitness>),
}

impl MutWireWitness {
    /// Formats the path which motivates something at the witness being &mut.
    /// Expected to be used in a sentence like `Because A{motivation} is of type &mut _`
    ///
    /// Examples:
    /// This => Becase A <is of type &mut _>
    /// Field => Becase A<.x is of type &mut _>
    /// Tuple => Becase A<#0 is of type &mut _>
    /// Array => Becase A<[..] is of type &mut _>
    /// Array,Field => Becase A<[..].a is of type &mut _>
    pub fn motivation(&self) -> String {
        match self {
            // TODO: T is a bad name
            MutWireWitness::This => format!(" is of type &mut"),
            MutWireWitness::Field(ident, rest) => format!(".{}{}", ident, rest.motivation()),
            MutWireWitness::TupleIndex(idx, rest) => format!("#{}{}", idx, rest.motivation()),
        }
    }
}

pub fn is_affine(ty: &ConcreteType) -> bool {
    match ty {
        ConcreteType::Tuple(inner) => inner.iter().any(is_affine),
        ConcreteType::Struct { name: _, members } => members.iter().any(|(_, ty)| is_affine(ty)),
        ConcreteType::Array { inner, size: _ } => is_affine(inner),
        ConcreteType::Enum { .. } => false,
        ConcreteType::Single { base, params: _ } => match base {
            spade_types::PrimitiveType::Int => false,
            spade_types::PrimitiveType::Uint => false,
            spade_types::PrimitiveType::Clock => false,
            spade_types::PrimitiveType::Bool => false,
            spade_types::PrimitiveType::Memory => false,
        },
        ConcreteType::Integer(_) => false,
        ConcreteType::Backward(_) => true,
        ConcreteType::Wire(_) => false,
    }
}

/*
Instances of Linear types and their use is represented as a tree, where leaf nodes
are fully linear types, and non-leaves are structs containing fully linear nodes.

For example: `let x: ((&mut A, &mut B), &mut C) = ..` is represented by

```
        [1]
       /   \
      /     \
    [2]     [3]
   /   \
 [4]   [5]
```

In addition, there is a map of aliases for nodes in the tree. Initially, this is
only populated by `x` which refers to the whole tree

```
x: [1]
```

Each node has an associated usage info, initially starting out as unused.

```
[1]: unused
[2]: unused
[3]: unused
[4]: unused
[5]: unused
```

The expression `x` with id 0 adds an additional referer to the corresponding node `[1]`
```
x: [1]
0: [1]
```

The expressions `#`, `.` and `Identifier` add aliases for instances. For example,
`x#0` with id 1 (where x is the expression discussed above (with id 0)) adds an alias to [2]

```
x: [1]
0: [1]
1: [2]
```

Assigning this expression to `y` adds yet another reference
```
x: [1]
0: [1]
1: [2]
y: [2]
```

Consuming `y`, for example via `a(y)` marks all the subnodes of that tree as used, taking
note of where that use was performed. Because all subnodes are unused, this is allowed

```
[1]: unused
[2]: unused
[3]: consumed(y)
[4]: consumed(y)
```

Attempting to consume `x` checks if the children are used, which fails. It will report
an error about the re-consumption.

Ignoring this error, the final check for unused linear types walks the tree looking for
unused leaf nodes. Used non-leaves are not an issue. If one is found, the path to it
can easily be reported
*/

#[derive(Clone, Debug)]
pub enum UsageInfo {
    Unlimited,
    Unused,
    Consumed(Loc<()>),
}

#[derive(Debug)]
struct AffineTree {
    pub kind: AffineTreeKind,
    pub aliases: Vec<Loc<ItemReference>>,
}

#[derive(Debug)]
enum AffineTreeKind {
    Leaf(UsageInfo),
    Struct(HashMap<Identifier, Rc<RefCell<AffineTree>>>),
    Tuple(Vec<Rc<RefCell<AffineTree>>>),
}

pub type ConsumptionError = (MutWireWitness, Loc<()>);

impl AffineTree {
    /// Attempts to mark this node as consumed, returning a witness to a node
    /// which is being doubly consumed if consumption is not possible.
    ///
    /// If consumption is possible, returns the new state of the tree.
    pub fn try_consume(&mut self, loc: Loc<()>) -> Result<(), ConsumptionError> {
        match &mut self.kind {
            AffineTreeKind::Leaf(state) => match state {
                UsageInfo::Unlimited => Ok(()),
                UsageInfo::Unused => {
                    let new_state = UsageInfo::Consumed(loc);
                    *state = new_state.clone();
                    Ok(())
                }
                UsageInfo::Consumed(prev) => Err((MutWireWitness::This, prev.clone())),
            },
            AffineTreeKind::Struct(members) => {
                members
                    .iter()
                    .map(|(ident, sub)| {
                        sub.borrow_mut().try_consume(loc).map_err(|(witness, loc)| {
                            (MutWireWitness::Field(ident.clone(), Box::new(witness)), loc)
                        })
                    })
                    .collect::<Result<_, ConsumptionError>>()?;
                Ok(())
            }
            AffineTreeKind::Tuple(members) => {
                members
                    .iter()
                    .enumerate()
                    .map(|(i, sub)| {
                        sub.borrow_mut().try_consume(loc).map_err(|(witness, loc)| {
                            (MutWireWitness::TupleIndex(i, Box::new(witness)), loc)
                        })
                    })
                    .collect::<Result<_, ConsumptionError>>()?;
                Ok(())
            }
        }
    }

    fn leaf(is_limited: bool) -> Self {
        let usage = if is_limited {
            UsageInfo::Unused
        } else {
            UsageInfo::Unlimited
        };

        Self {
            kind: AffineTreeKind::Leaf(usage),
            aliases: vec![],
        }
    }

    fn tuple(inner: Vec<Rc<RefCell<AffineTree>>>) -> Self {
        Self {
            kind: AffineTreeKind::Tuple(inner),
            aliases: vec![],
        }
    }

    fn struct_(fields: HashMap<Identifier, Rc<RefCell<AffineTree>>>) -> Self {
        Self {
            kind: AffineTreeKind::Struct(fields),
            aliases: vec![],
        }
    }

    pub fn add_alias(&mut self, alias: Loc<ItemReference>) {
        self.aliases.push(alias)
    }

    pub fn assume_tuple(&self) -> &Vec<Rc<RefCell<AffineTree>>> {
        match &self.kind {
            AffineTreeKind::Tuple(inner) => &inner,
            _ => panic!("Assumed tree was tuple, got {:?}", self.kind),
        }
    }

    pub fn assume_struct(&self) -> &HashMap<Identifier, Rc<RefCell<AffineTree>>> {
        match &self.kind {
            AffineTreeKind::Struct(inner) => &inner,
            _ => panic!("Assumed tree was tuple, got {:?}", self.kind),
        }
    }

    pub fn check_unused(&self) -> Result<(), MutWireWitness> {
        match &self.kind {
            AffineTreeKind::Leaf(usage) => match usage {
                UsageInfo::Unlimited => Ok(()),
                UsageInfo::Unused => Err(MutWireWitness::This),
                UsageInfo::Consumed(_) => Ok(()),
            },
            AffineTreeKind::Struct(fields) => {
                for (name, sub) in fields {
                    match sub.borrow().check_unused() {
                        Ok(_) => {}
                        Err(witness) => {
                            return Err(MutWireWitness::Field(name.clone(), Box::new(witness)))
                        }
                    }
                }
                Ok(())
            }
            AffineTreeKind::Tuple(members) => {
                for (i, member) in members.iter().enumerate() {
                    match member.borrow().check_unused() {
                        Ok(_) => {}
                        Err(witness) => {
                            return Err(MutWireWitness::TupleIndex(i, Box::new(witness)))
                        }
                    }
                }
                Ok(())
            }
        }
    }
}

fn build_affine_tree(source_loc: Loc<()>, ty: &ConcreteType) -> AffineTree {
    match ty {
        ConcreteType::Tuple(inner) => {
            let inner = inner
                .iter()
                .map(|ty| Rc::new(RefCell::new(build_affine_tree(source_loc, ty))))
                .collect();
            AffineTree::tuple(inner)
        }
        ConcreteType::Struct { name: _, members } => {
            let inner = members
                .iter()
                .map(|(name, ty)| {
                    (
                        name.clone(),
                        Rc::new(RefCell::new(build_affine_tree(source_loc, ty))),
                    )
                })
                .collect();
            AffineTree::struct_(inner)
        }
        ConcreteType::Array { inner, size: _ } => {
            if is_affine(inner) {
                // Since we can't keep track of dynamic indices, we won't allow
                // indexing on arrays. We therefore have to resort to treating the whole
                // thing as one giant affine type, and require destructuring
                AffineTree::leaf(true)
            } else {
                AffineTree::leaf(false)
            }
        }
        ConcreteType::Enum { .. } => AffineTree::leaf(false),
        ConcreteType::Single { base, params: _ } => match base {
            spade_types::PrimitiveType::Int => AffineTree::leaf(false),
            spade_types::PrimitiveType::Uint => AffineTree::leaf(false),
            spade_types::PrimitiveType::Clock => AffineTree::leaf(false),
            spade_types::PrimitiveType::Bool => AffineTree::leaf(false),
            spade_types::PrimitiveType::Memory => AffineTree::leaf(false),
        },
        ConcreteType::Integer(_) => AffineTree::leaf(false),
        ConcreteType::Backward(_) => AffineTree::leaf(true),
        ConcreteType::Wire(_) => AffineTree::leaf(false),
    }
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub enum ItemReference {
    Name(NameID),
    Anonymous(u64),
}
impl WithLocation for ItemReference {}

impl ItemReference {
    fn anonymous(n: &Loc<u64>) -> Loc<Self> {
        Self::Anonymous(n.inner.clone()).at_loc(&n)
    }
    fn name(n: &Loc<NameID>) -> Loc<Self> {
        Self::Name(n.inner.clone()).at_loc(&n)
    }
}

impl std::fmt::Display for ItemReference {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ItemReference::Name(n) => write!(f, "{n}"),
            ItemReference::Anonymous(id) => write!(f, "{id}"),
        }
    }
}

pub struct AffineState {
    /// The trees visible via references, either names or expression IDs. Multiple
    /// references can refer to the same tree
    trees: HashMap<ItemReference, Rc<RefCell<AffineTree>>>,
}

impl AffineState {
    pub fn new() -> Self {
        Self {
            trees: HashMap::new(),
        }
    }

    /// If there is an affine tree which has a leaf node that is unused, reports it as an
    /// item reference and a witness for something that needs to be used.
    ///
    /// The item reference is chosen to be as useful to the user as possible. If there
    /// is a name alias for this item, it is used, if not, an expression reference is used
    pub fn check_unused(&self) -> Result<(), (Loc<ItemReference>, MutWireWitness)> {
        for tree in self.trees.values() {
            let tree = tree.borrow();
            match tree.check_unused() {
                Ok(()) => {}
                Err(witness) => {
                    let mut alias_priority = tree.aliases.clone();
                    alias_priority.sort_by(|l, r| match (&l.inner, &r.inner) {
                        (ItemReference::Name(_), ItemReference::Name(_)) => Ordering::Equal,
                        (ItemReference::Name(_), ItemReference::Anonymous(_)) => Ordering::Less,
                        (ItemReference::Anonymous(_), ItemReference::Name(_)) => Ordering::Greater,
                        (ItemReference::Anonymous(_), ItemReference::Anonymous(_)) => {
                            Ordering::Equal
                        }
                    });

                    // NOTE: Safe unwrap. Since we accessed this tree from `self.trees` it was
                    // in the hash map and must have at least one alias
                    let best_alias = alias_priority.first().unwrap();
                    return Err((best_alias.clone(), witness));
                }
            }
        }
        Ok(())
    }

    pub fn push_type(&mut self, reference: Loc<ItemReference>, ty: &ConcreteType, ctx: &AffineCtx) {
        let tree = Rc::new(RefCell::new(build_affine_tree(reference.loc(), ty)));

        tree.borrow_mut().add_alias(reference.clone());
        self.trees.insert(reference.inner.clone(), tree);
    }

    #[tracing::instrument(level = "trace", skip_all, fields(%expr_id))]
    // Inserts a new [AffineTree] for the specified expression.
    pub fn push_new_expression(&mut self, expr_id: &Loc<u64>, ctx: &AffineCtx) {
        // Generic arguments can not be affine types, so we can ignore non-fully known types
        if let Some(ty) = &ctx
            .type_state
            .try_get_type_of_id(expr_id.inner, ctx.symtab, ctx.types)
        {
            let reference = ItemReference::Anonymous(expr_id.inner).at_loc(&expr_id);
            self.push_type(reference, ty, ctx);
        }
    }

    #[tracing::instrument(level = "trace", skip_all, fields(%name))]
    pub fn push_new_name(&mut self, name: &Loc<NameID>, ctx: &AffineCtx) {
        // Generic arguments can not be affine types, so we can ignore non-fully known types
        if let Some(ty) = &ctx
            .type_state
            .try_get_type_of_name(name, ctx.symtab, ctx.types)
        {
            let reference = ItemReference::Name(name.inner.clone()).at_loc(name);
            self.push_type(reference, ty, ctx);
        }
    }

    /// Merges two ItemReferences into a single tree. Exactly one of the items must have a
    /// pre-existing tree, or the pre-existing trees must be the same trees, otherwise it panics
    #[tracing::instrument(level = "trace", skip_all, fields(%lhs, %rhs))]
    pub fn merge(&mut self, lhs: Loc<ItemReference>, rhs: Loc<ItemReference>, ctx: &AffineCtx) {
        let lhs_tree = self.trees.get(&lhs).clone();
        let rhs_tree = self.trees.get(&rhs).clone();

        let (old_tree, new_name) = match (lhs_tree, rhs_tree) {
            (Some(l), None) => (l, rhs),
            (None, Some(r)) => (r, lhs),
            (Some(l), Some(r)) => {
                assert!(l.as_ptr() == r.as_ptr());
                return;
            }
            (None, None) => {
                panic!("Attempting to merge {lhs} with {rhs} but neither had a previous tree")
            }
        };

        old_tree.borrow_mut().add_alias(new_name.clone());
        self.trees.insert(new_name.inner, old_tree.clone());
    }

    #[tracing::instrument(level = "trace", skip_all, fields(%from, %to))]
    pub fn add_alias_name(&mut self, from: Loc<u64>, to: &Loc<NameID>, ctx: &AffineCtx) {
        self.merge(
            ItemReference::anonymous(&from),
            ItemReference::name(to),
            ctx,
        );
    }

    fn alias_subtree<F>(&mut self, to: Loc<u64>, base_expr: u64, idx: F)
        where F: Fn(&AffineTree) -> Rc<RefCell<AffineTree>>
    {
        let base_tree_rc = Rc::clone(
            self.trees
                .get(&ItemReference::Anonymous(base_expr))
                .expect("Adding an alias to an expression which has no tree"),
        );

        let base_tree = base_tree_rc.borrow();

        let subtree = idx(&base_tree);

        let new_alias = ItemReference::Anonymous(to.inner).at_loc(&to);
        subtree.borrow_mut().add_alias(new_alias.clone());
        self.trees.insert(new_alias.inner, subtree);
    }


    /// Adds `from` as an alias to the tree at `base_expr#tuple_member`. Panics if base_expr is not
    /// a tuple with at least idx elements
    #[tracing::instrument(level = "trace", skip_all, fields(%base_expr, %idx, %to))]
    pub fn alias_tuple_memeber(
        &mut self,
        to: Loc<u64>,
        base_expr: u64,
        idx: &Loc<u128>,
    ) {
        self.alias_subtree(to, base_expr, |base_tree| {
            let subtrees = base_tree.assume_tuple();
            Rc::clone(&subtrees[idx.inner as usize])
        });
    }

    /// Adds `from` as an alias to the tree at `base_expr#tuple_member`. Panics if base_expr is not
    /// a tuple with at least idx elements
    #[tracing::instrument(level = "trace", skip_all, fields(%base_expr, %field, %to))]
    pub fn alias_struct_memeber(
        &mut self,
        to: Loc<u64>,
        base_expr: u64,
        field: &Loc<Identifier>,
    ) {
        self.alias_subtree(to, base_expr, |base_tree| {
            let subtrees = base_tree.assume_struct();
            Rc::clone(&subtrees[field])
        });
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn push_pattern(&mut self, pat: &Pattern, ctx: &AffineCtx) {
        match &pat.kind {
            PatternKind::Integer(_) => {}
            PatternKind::Bool(_) => {}
            PatternKind::Name { name, pre_declared } => {
                let pat_id = pat.id;
                let id_loc = pat_id.at_loc(name);
                if !pre_declared {
                    self.push_new_expression(&id_loc, ctx);
                }
                self.merge(
                    ItemReference::anonymous(&id_loc),
                    ItemReference::name(name),
                    ctx,
                );
            }
            PatternKind::Tuple(inner) => {
                for pat in inner {
                    self.push_pattern(pat, ctx)
                }
            }
            PatternKind::Type(_, args) => {
                for arg in args {
                    self.push_pattern(&arg.value.inner, ctx);
                }
            }
        }
    }

    pub fn consume_expression(&mut self, expr: &Loc<Expression>) -> Result<(), Error> {
        self.consume_id(expr.map_ref(|e| e.id))
    }

    #[tracing::instrument(level = "trace", skip_all, fields(%id))]
    pub fn consume_id(&mut self, id: Loc<u64>) -> Result<(), Error> {
        // NOTE: This is fairly inefficient at the moment. It might be better to try
        // and use something like a multi-map for several references to the same tree

        // Build a list of the trees which we should mark as consumed by walking all
        // the aliases
        let new_ref = ItemReference::Anonymous(id.inner);
        let mut references = vec![new_ref];
        let mut seen_pointers = vec![];
        let mut trees_to_consume = vec![];

        while let Some(reference) = references.pop() {
            let tree = self.trees.get(&reference).expect(&format!(
                "Failed to find affine tree for {reference} when consuming {id}"
            ));

            if seen_pointers.contains(&tree.as_ptr()) {
                break;
            }
            seen_pointers.push(tree.as_ptr());
            trees_to_consume.push(tree);

            for alias in &tree.borrow().aliases {
                references.push(alias.inner.clone());
            }
        }

        // For each *unique* tree, try to consume the trees
        for tree in trees_to_consume {
            trace!("Consuming tree {}", tree.as_ptr() as usize);
            tree.borrow_mut()
                .try_consume(id.loc())
                .map_err(|(witness, previous_use)| Error::UseOfConsumedAffineName {
                    new_use: id.loc(),
                    previous_use,
                    witness,
                })?;
        }

        Ok(())
    }
}
