use itertools::Itertools;

use crate::asm::Reg;
use crate::identifiers::{BlockName, VarName};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::hash::Hash;
use std::{fmt, ops};

/// The trivial (placeholder) analysis metadata.
/// This is used when no analysis has been performed.
#[derive(Clone, Copy, Default)]
pub struct Nil;

/* ------------------------------- Allocation ------------------------------- */

/// The allocation of a variable to a register or a stack slot.
/// `S` may refer to the stack slot number.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Allocation {
    /// The variable is allocated to a register
    Reg(Reg),
    /// The variable is spilled to the stack.
    /// Given `s: i32`, `-8 * s` is the stack offset relative to rsp.
    Spill(i32),
}

impl Allocation {
    pub fn as_reg(self) -> Option<Reg> {
        match self {
            Allocation::Reg(reg) => Some(reg),
            Allocation::Spill(_) => None,
        }
    }

    pub fn as_spill(self) -> Option<i32> {
        match self {
            Allocation::Reg(_) => None,
            Allocation::Spill(slot) => Some(slot),
        }
    }
}

impl fmt::Display for Allocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Allocation::Reg(reg) => write!(f, "{}", reg),
            Allocation::Spill(slot) => write!(f, "<{}>", slot),
        }
    }
}

/* ---------------------------- Liveness Analysis --------------------------- */

#[derive(Clone)]
pub struct LiveSet(pub BTreeSet<VarName>);

impl LiveSet {
    pub fn new() -> Self {
        LiveSet(BTreeSet::new())
    }
}

impl fmt::Display for LiveSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use crate::pretty::*;
        fmt::Display::fmt("[", f)?;
        fmt::Display::fmt(&Separated(&self.0.iter(), ", "), f)?;
        fmt::Display::fmt("]", f)
    }
}

impl ops::Deref for LiveSet {
    type Target = BTreeSet<VarName>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ops::DerefMut for LiveSet {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl FromIterator<VarName> for LiveSet {
    fn from_iter<T: IntoIterator<Item = VarName>>(iter: T) -> Self {
        LiveSet(BTreeSet::from_iter(iter))
    }
}

impl IntoIterator for LiveSet {
    type Item = VarName;
    type IntoIter = std::collections::btree_set::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        let LiveSet(live) = self;
        live.into_iter()
    }
}

impl<'a> IntoIterator for &'a LiveSet {
    type Item = &'a VarName;
    type IntoIter = std::collections::btree_set::Iter<'a, VarName>;

    fn into_iter(self) -> Self::IntoIter {
        let LiveSet(live) = self;
        live.iter()
    }
}

/* ---------------------------- UnusedBlockParam ---------------------------- */

/// Used in `UnusedRemover` to keep track of the unused parameters for each block.
pub struct UnusedBlockParams(pub HashMap<BlockName, HashSet<usize>>);

impl UnusedBlockParams {
    pub fn new() -> Self {
        UnusedBlockParams(HashMap::new())
    }
}

impl fmt::Display for UnusedBlockParams {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let res =
            Vec::from_iter(self.0.iter().filter(|(_, p)| !p.is_empty()).sorted_by_key(|(b, _)| *b));
        if res.is_empty() {
            write!(f, "(none)")
        } else {
            write!(
                f,
                "{}",
                Vec::from_iter(res.iter().map(|(b, p)| format!(
                    "{}: {}",
                    b,
                    p.iter().map(|p| format!("param #{}", p)).collect::<Vec<_>>().join(", ")
                )))
                .join("\n")
            )
        }
    }
}

impl ops::Deref for UnusedBlockParams {
    type Target = HashMap<BlockName, HashSet<usize>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ops::DerefMut for UnusedBlockParams {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/* ------------------------------ UnusedVarSet ------------------------------ */

/// Used in `UnusedRemover` to keep track of the unused variables for each block.
pub struct UnusedVarSet(pub HashSet<VarName>);

impl UnusedVarSet {
    pub fn new() -> Self {
        UnusedVarSet(HashSet::new())
    }
}

impl fmt::Display for UnusedVarSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            write!(f, "(none)")
        } else {
            write!(f, "{}", Vec::from_iter(self.0.iter().map(|v| v.to_string())).join(", "))
        }
    }
}

impl ops::Deref for UnusedVarSet {
    type Target = HashSet<VarName>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ops::DerefMut for UnusedVarSet {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/* ------------------------------ Reassignments ----------------------------- */

/// The fresh variables for each variable reference.
/// `old_var -> new_var`
#[derive(Clone)]
pub struct Reassignments(HashMap<VarName, VarName>);

impl Reassignments {
    pub fn new() -> Self {
        Reassignments(HashMap::new())
    }
}

impl ops::Deref for Reassignments {
    type Target = HashMap<VarName, VarName>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ops::DerefMut for Reassignments {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/* ------------------------ Perfect Elimination Order ----------------------- */

/// The perfect elimination order of the variables.
///
/// Used in register allocation.
pub struct PerfectEliminationOrder(pub Vec<VarName>);

impl PerfectEliminationOrder {
    pub fn new() -> Self {
        PerfectEliminationOrder(Vec::new())
    }
}

impl fmt::Display for PerfectEliminationOrder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Vec::from_iter(self.0.iter().map(|v| v.to_string())).join(" -> "))
    }
}

impl ops::Deref for PerfectEliminationOrder {
    type Target = Vec<VarName>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ops::DerefMut for PerfectEliminationOrder {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Extend<VarName> for PerfectEliminationOrder {
    fn extend<T: IntoIterator<Item = VarName>>(&mut self, iter: T) {
        self.0.extend(iter);
    }
}

impl IntoIterator for PerfectEliminationOrder {
    type Item = VarName;
    type IntoIter = std::iter::Rev<std::vec::IntoIter<Self::Item>>;

    fn into_iter(self) -> Self::IntoIter {
        // Here're two mutations:

        // 1. don't reverse the order
        // self.0.into_iter()

        // 2. sort the order
        // use itertools::Itertools as _;
        // self.0.into_iter().sorted();

        self.0.into_iter().rev()
    }
}

impl<'a> IntoIterator for &'a PerfectEliminationOrder {
    type Item = &'a VarName;
    type IntoIter = std::iter::Rev<std::slice::Iter<'a, VarName>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().rev()
    }
}

/* ---------------------------- Undirected Graph ---------------------------- */

/// An undirected graph as an "adjacency list", i.e., a map from
/// vertices to the set of neighbors.
///
/// Invariant: Edges are undirected so v1 is in v2s set of neighbors if
/// and only if v2 is in v1s set of neigbhors.
///
/// Used as the interference graph.
#[derive(Debug, Clone)]
pub struct Graph<V> {
    g: HashMap<V, HashSet<V>>,
}

impl<V: fmt::Display + Ord> fmt::Display for Graph<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for v in self.g.keys().sorted() {
            writeln!(f, "vertex {}", v)?;
        }
        for (v1, v2s) in self.g.iter().sorted_by_key(|(v, _)| *v) {
            for v2 in v2s.iter().sorted() {
                writeln!(f, "edge {} {}", v1, v2)?;
            }
        }
        Ok(())
    }
}

impl<V: Eq + Hash> Graph<V> {
    /// Returns the empty graph
    pub fn new() -> Graph<V> {
        Graph { g: HashMap::new() }
    }

    /// Inserts a vertex into the graph
    pub fn insert_vertex(&mut self, v: V) {
        match self.g.get(&v) {
            None => {
                self.g.insert(v, HashSet::new());
            }
            Some(_) => {}
        }
    }

    /// Inserts an (undirected) edge between v1 and v2
    pub fn insert_edge(&mut self, v1: V, v2: V)
    where
        V: Clone,
    {
        self.insert_vertex(v1.clone());
        self.insert_vertex(v2.clone());
        match self.g.get_mut(&v1) {
            None => unreachable!(),
            Some(es1) => {
                let _ = es1.insert(v2.clone());
            }
        }
        match self.g.get_mut(&v2) {
            None => unreachable!(),
            Some(es1) => {
                let _ = es1.insert(v1);
            }
        }
    }

    /// Returns a vector of all the vertices in the graph
    pub fn vertices(&self) -> Vec<V>
    where
        V: Clone,
    {
        self.g.keys().cloned().collect()
    }

    /// Given a vertex v, returns None if the v is not present in the
    /// graph and otherwise returns the set of vertices that v has an
    /// edge to.
    pub fn neighbors(&self, v: &V) -> Option<&HashSet<V>> {
        self.g.get(v)
    }

    /// Removes a vertex from the graph, returning true if the vertex
    /// was present and false if it wasn't
    pub fn remove_vertex(&mut self, v: &V) -> bool {
        let ans = self.g.remove(v).is_some();
        for es in self.g.values_mut() {
            es.remove(v);
        }
        ans
    }

    /// Returns the number of vertices in the graph
    pub fn num_vertices(&self) -> usize {
        self.g.keys().len()
    }

    /// Checks if an edge between v1 and v2 exists
    pub fn contains_edge(&self, v1: &V, v2: &V) -> bool {
        match self.g.get(v1) {
            Some(neigbhors) => neigbhors.contains(v2),
            None => false,
        }
    }
}

impl<V: Eq + Hash + Ord> Graph<V> {
    /// Generates a dot file for the graph.
    pub fn dot(&self, path: impl AsRef<std::path::Path>)
    where
        V: Clone + fmt::Display,
    {
        use itertools::Itertools as _;
        use layout::backends::svg::SVGWriter;
        use layout::core::base::Orientation;
        use layout::core::geometry::Point;
        use layout::core::style::*;
        use layout::core::utils::save_to_file;
        use layout::std_shapes::shapes::*;
        use layout::topo::layout::VisualGraph;
        use std::collections::BTreeMap;

        let edges = {
            let mut edges = Vec::new();
            let mut visited = HashSet::new();
            for (v1, v2s) in BTreeMap::from_iter(self.g.iter()) {
                visited.insert(v1);
                for v2 in v2s.iter().sorted() {
                    if !visited.contains(v2) {
                        edges.push((v1, v2));
                    }
                }
            }
            edges
        };

        let mut vg = VisualGraph::new(Orientation::LeftToRight);
        let mut nodes = HashMap::new();
        for v in self.vertices() {
            let handler = vg.add_node(Element::create(
                ShapeKind::new_circle(&v.to_string()),
                StyleAttr::simple(),
                Orientation::LeftToRight,
                Point::new(100., 100.),
            ));
            nodes.insert(v, handler);
        }

        for (v1, v2) in edges {
            vg.add_edge(
                Arrow::new(
                    LineEndKind::None,
                    LineEndKind::None,
                    LineStyleKind::Normal,
                    "",
                    &StyleAttr::simple(),
                    &None,
                    &None,
                ),
                nodes[&v1],
                nodes[&v2],
            );
        }

        if nodes.is_empty() {
            eprintln!("No nodes in the graph, not generating interference graph");
            return;
        }

        let mut svg = SVGWriter::new();
        vg.do_it(false, false, false, &mut svg);
        let content = svg.finalize();

        let path = path.as_ref().to_str().expect("Invalid path");
        let res = save_to_file(path, &content);
        if let Result::Err(err) = res {
            eprintln!("Could not write the file {}", path);
            eprintln!("Error {}", err);
            return;
        }
    }
}

/* -------------------------------- Coloring -------------------------------- */

/// The coloring of the variables to the registers or stack slots.
/// `i32` refers to the stack slot number.
pub struct Coloring(pub HashMap<VarName, Allocation>);

impl Coloring {
    pub fn new() -> Self {
        Coloring(HashMap::new())
    }
}

impl ops::Deref for Coloring {
    type Target = HashMap<VarName, Allocation>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ops::DerefMut for Coloring {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl fmt::Display for Coloring {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (v, a) in self.0.iter().sorted_by_key(|(v, _)| *v) {
            writeln!(f, "{} -> {}", v, a)?;
        }
        Ok(())
    }
}
