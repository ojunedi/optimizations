use crate::asm::Reg;
use clap::ValueEnum;
use std::collections::HashSet;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Target {
    /// Raw AST
    AST,
    /// Resolved AST
    ResolvedAST,
    /// SSA
    SSA,
    /// Interference Graph
    Graph,
    /// Elimination Order
    ElimOrder,
    /// Register Allocation Result (via Graph Coloring)
    Coloring,
    /// x86_64 Assembly Code
    Asm,
    /// Binary executable
    Exe,
}
pub use Target::*;

pub struct CompilerConf {
    pub optimizations: HashSet<Optimization>,
    pub verbose: Verbosity,
}

impl CompilerConf {
    pub fn new(optimizations: impl IntoIterator<Item = Optimization>, verbose: Verbosity) -> Self {
        Self { optimizations: optimizations.into_iter().collect(), verbose }
    }
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Optimization {
    /// Copy Propagation - replace `x` with `y` if an instruction `x = y` exists
    #[value(name = "cp")]
    CopyPropagation,
    /// Assertion Removal - removes integer type assertions
    #[value(name = "ar")]
    AssertionRemoval,
    /// Dead Code Elimination - remove unused variables and parameters
    #[value(name = "dce")]
    DeadCodeElimination,
    /// Variable Lifetime Splitting - variable lifetime splitting
    #[value(name = "vls")]
    VariableLifetimeSplitting,
}
impl Optimization {
    pub fn all() -> HashSet<Optimization> {
        [
            Optimization::AssertionRemoval,
            Optimization::CopyPropagation,
            Optimization::DeadCodeElimination,
            Optimization::VariableLifetimeSplitting,
        ]
        .into()
    }
}

#[derive(Debug, Clone)]
pub struct OptimizationCollection {
    optimizations: HashSet<Optimization>,
}
impl std::str::FromStr for OptimizationCollection {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // split on commas
        if s == "all" {
            return Ok(OptimizationCollection { optimizations: Optimization::all() });
        }
        let optimizations: Vec<&str> = s.split(',').collect();
        let optimizations = optimizations
            .into_iter()
            .map(|o| {
                Optimization::from_str(o, true).map_err(|e| format!("Invalid optimization: {}", e))
            })
            .collect::<Result<_, _>>()?;
        Ok(OptimizationCollection { optimizations })
    }
}
impl IntoIterator for OptimizationCollection {
    type Item = Optimization;
    type IntoIter = std::collections::hash_set::IntoIter<Optimization>;

    fn into_iter(self) -> Self::IntoIter {
        self.optimizations.into_iter()
    }
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Verbosity {
    /// Only print the final output.
    ///
    /// Provides a canonical output for autograder.
    Minimalistic,
    /// Print the final output and crucial intermediate steps.
    ///
    /// Suitable for learning and debugging.
    Moderate,
    /// Print the final output and all intermediate steps.
    ///
    /// Suitable for learning and debugging.
    Mouthful,
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum RegisterCollection {
    #[value(name = "all")]
    AllocatableAll,
    #[value(name = "volatile", alias = "caller")]
    AllocatableVolatile,
    #[value(name = "non-volatile", alias = "callee")]
    AllocatableNonVolatile,
    #[value(name = "none")]
    None,
}

#[derive(Debug, Clone)]
pub struct RegisterSelection {
    base: RegisterCollection,
    additions: Vec<Reg>,
    removals: Vec<Reg>,
}

impl RegisterSelection {
    pub fn to_registers(&self) -> Vec<Reg> {
        // Start with the base collection
        let mut regs: Vec<Reg> = match self.base {
            RegisterCollection::AllocatableAll => Reg::ALLOCATABLE.to_vec(),
            RegisterCollection::AllocatableVolatile => Reg::ALLOCATABLE_VOLATILE.to_vec(),
            RegisterCollection::AllocatableNonVolatile => Reg::ALLOCATABLE_NON_VOLATILE.to_vec(),
            RegisterCollection::None => vec![],
        };

        // Add any registers in the additions list
        for reg in &self.additions {
            if !regs.contains(reg) {
                regs.push(*reg);
            }
        }

        // Remove any registers in the removals list
        for reg in &self.removals {
            if let Some(i) = regs.iter().position(|r| r == reg) {
                regs.remove(i);
            }
        }
        regs
    }
}

impl std::str::FromStr for RegisterSelection {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use regex::Regex;

        let re = Regex::new(r"([^\+-]+)|([\+-][^\+-]+)").unwrap();
        // Split on + or - but keep the delimiters
        let parts: Vec<&str> = re.find_iter(s).map(|m| m.as_str()).collect();
        if parts.is_empty() {
            return Err("Empty register selection".to_string());
        }

        // Parse the base collection
        let base = RegisterCollection::from_str(parts[0], true)
            .map_err(|_| format!("Invalid register collection: {}", parts[0]))?;

        let mut selection = RegisterSelection { base, additions: Vec::new(), removals: Vec::new() };

        // Process the rest of the parts
        for part in &parts[1..] {
            if part.starts_with('+') {
                let reg_name = &part[1..];
                let reg = Reg::from_str(reg_name, true)
                    .map_err(|_| format!("Invalid register to add: {}", reg_name))?;
                selection.additions.push(reg);
            } else if part.starts_with('-') {
                let reg_name = &part[1..];
                let reg = Reg::from_str(reg_name, true)
                    .map_err(|_| format!("Invalid register to remove: {}", reg_name))?;
                selection.removals.push(reg);
            } else {
                return Err(format!("Invalid modifier format: {}", part));
            }
        }

        Ok(selection)
    }
}
