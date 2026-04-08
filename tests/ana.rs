pub use snake_optimizations::ana::*;
use std::collections::{HashMap, HashSet};

pub fn valid_coloring(
    rig: &Graph<String>, assignment: &HashMap<String, Allocation>,
) -> Result<(), String> {
    let mut rev_assignment: HashMap<Allocation, HashSet<String>> = HashMap::new();

    use std::collections::hash_map::Entry;
    for (var, loc) in assignment.iter() {
        match rev_assignment.entry(*loc) {
            Entry::Occupied(mut occ) => {
                let vars = occ.get_mut();
                for var2 in vars.iter() {
                    if rig.contains_edge(var, var2) {
                        return Err(format!(
                            "Your graph coloring algorithm assigns the interfering vertices {} and {} to the same location: {}",
                            var, var2, loc
                        ));
                    }
                }
            }
            Entry::Vacant(vacancy) => {
                let mut h = HashSet::new();
                h.insert(var.clone());
                vacancy.insert(h);
            }
        }
    }
    Ok(())
}

pub fn count_spills(assignment: &HashMap<String, Allocation>) -> usize {
    assignment
        .values()
        .filter_map(|loc| match loc {
            Allocation::Spill(i) => Some(i),
            Allocation::Reg(_) => None,
        })
        .count()
}

pub fn should_be_same_graph(
    user_g: &Graph<String>, expected_g: &Graph<String>,
) -> Result<(), String> {
    println!("user_graph:\n{}", user_g);
    println!("xpct_graph:\n{}", expected_g);
    let u_vs: HashSet<String> = user_g.vertices().iter().cloned().collect();
    let e_vs: HashSet<String> = expected_g.vertices().iter().cloned().collect();
    if !u_vs.is_superset(&e_vs) {
        return Err(
            "You did not include all necessary variables in your register interference graph"
                .to_string(),
        );
    } else if !u_vs.is_subset(&e_vs) {
        return Err(
            "You included variables in your register interference graph that you shouldn't have"
                .to_string(),
        );
    }
    // now we know they have the same vars
    for v in u_vs {
        let u_es = user_g.neighbors(&v).unwrap();
        let e_es = expected_g.neighbors(&v).unwrap();

        if !u_es.is_subset(e_es) {
            Err(format!("Your interference graph contains an unnecessary conflict"))?;
        } else if !u_es.is_superset(e_es) {
            Err(format!("Your interference graph is missing a conflict"))?;
        }
    }
    Ok(())
}

#[allow(unused)]
pub fn full_sub_graph(sub_g: &Graph<String>, sup_g: &Graph<String>) -> Result<(), String> {
    println!("sub_graph: {:?}", sub_g);
    println!("sup_graph: {:?}", sup_g);
    let sub_vs: HashSet<String> = sub_g.vertices().iter().cloned().collect();
    let sup_vs: HashSet<String> = sup_g.vertices().iter().cloned().collect();

    if !sub_vs.is_superset(&sup_vs) {
        return Err(
            "You did not include all variables in your register interference graph".to_string()
        );
    } else if !sub_vs.is_subset(&sup_vs) {
        return Err(
            "You included variables in your register interference graph that you shouldn't have"
                .to_string(),
        );
    }

    for v in sub_vs {
        let sub_neighbors = sub_g.neighbors(&v).unwrap();
        let sup_neighbors = sup_g.neighbors(&v).unwrap();

        if !sub_neighbors.is_subset(sup_neighbors) {
            let v2 = sub_neighbors.difference(sup_neighbors).next().unwrap();
            return Err(format!("Your interference graph is missing at least one conflict"));
        }
    }
    Ok(())
}
