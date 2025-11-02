// Blood on the Clocktower SAT-based reasoning engine
//
// Current limitations and known bugs:
//
// - **CRITICAL BUG**: Placeholder encoding has issues with cardinality constraints
//   The sequential counter implementation for "exactly N" sometimes produces invalid models
//   that violate the count constraints. This manifests as placeholders being assigned the
//   same role (duplicates) or total role count being less than specified.
//   TODO: Replace sequential counter with a proven-correct implementation (totalizer, sorting network)
//   or use an external cardinality constraint library.
//
// - Only supports unique roles per bag (no duplicates)
//   TODO: Support experimental characters like Village Idiot, Legion, Riot that allow duplicates
//   This requires tracking role counts instead of just presence/absence
//
// - Modifier role encoding assumes at most one modifier role present
//   TODO: Generalize to handle multiple stacking modifiers (e.g., Baron + Godfather + Vigormortis)
//   Current workaround works for Trouble Brewing (only Baron has modifiers)
//
// - Placeholder syntax supports:
//   - `?name?` - unconstrained role variable
//   - `?team:name?` - role variable constrained to team (tf/os/mn/dm shorthands supported)
//   - Not yet: `?bag?` - entire bag as placeholder

use clap::{Parser, Subcommand};
use rustsat::instances::BasicVarManager;
use rustsat::instances::SatInstance;
use rustsat::solvers::Solve;
use rustsat::solvers::SolverResult;
use rustsat::types::{Clause, TernaryVal};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Team {
    Townsfolk,
    Outsider,
    Minion,
    Demon,
}

impl Team {
    fn from_str_or_shorthand(s: &str) -> Option<Team> {
        match s.to_lowercase().as_str() {
            "townsfolk" | "tf" => Some(Team::Townsfolk),
            "outsider" | "os" => Some(Team::Outsider),
            "minion" | "mn" => Some(Team::Minion),
            "demon" | "dm" => Some(Team::Demon),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum SetupModifier {
    /// Baron: removes 2 townsfolk, adds 2 outsiders
    AdjustCounts {
        remove_townsfolk: u8,
        add_outsiders: u8,
    },
}

macro_rules! define_roles {
    (
        $(
            $role:ident: $name:literal => {
                team: $team:ident,
                ability: $ability:literal
                $(, all_nights: $all_nights:expr)?
                $(, first_night: $first_night:expr)?
                $(, other_nights: $other_nights:expr)?
                $(, setup: $setup:expr)?
            }
        ),* $(,)?
    ) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        #[allow(non_camel_case_types)]
        enum Role {
            $($role,)*
        }

        impl Role {
            const fn name(&self) -> &'static str {
                match self {
                    $(Role::$role => $name,)*
                }
            }

            const fn team(&self) -> Team {
                match self {
                    $(Role::$role => Team::$team,)*
                }
            }

            #[allow(dead_code)]
            const fn ability(&self) -> &'static str {
                match self {
                    $(Role::$role => $ability,)*
                }
            }

            #[allow(dead_code)]
            const fn first_night(&self) -> bool {
                match self {
                    $(Role::$role => define_roles!(@first_night $($all_nights)? $($first_night)?),)*
                }
            }

            #[allow(dead_code)]
            const fn other_nights(&self) -> bool {
                match self {
                    $(Role::$role => define_roles!(@other_nights $($all_nights)? $($other_nights)?),)*
                }
            }

            fn setup_modifier(&self) -> Option<SetupModifier> {
                match self {
                    $(Role::$role => define_roles!(@setup $($setup)?),)*
                }
            }

            const fn all() -> &'static [Role] {
                &[$(Role::$role,)*]
            }

            /// Maximum number of times this role can appear in a game
            /// Most roles can only appear once (returns 1)
            /// Experimental roles like Village Idiot can appear multiple times
            const fn max_count(&self) -> u8 {
                match self {
                    Role::VillageIdiot => 3, // Base + up to 2 extras
                    // Role::Legion => u8::MAX, // Legion has no limit
                    _ => 1, // Standard roles can only appear once
                }
            }
        }
    };

    // Helper: first_night - handles all_nights shorthand
    (@first_night true) => { true };           // all_nights: true
    (@first_night $first:expr) => { $first };  // first_night: <expr>
    (@first_night) => { false };               // nothing specified

    // Helper: other_nights - handles all_nights shorthand
    (@other_nights true) => { true };           // all_nights: true
    (@other_nights $other:expr) => { $other };  // other_nights: <expr>
    (@other_nights) => { false };               // nothing specified

    // Helper: convert optional setup modifier
    (@setup $val:expr) => { Some($val) };
    (@setup) => { None };
}

// Define all Trouble Brewing roles
define_roles! {
    // Townsfolk
    Washerwoman: "Washerwoman" => {
        team: Townsfolk,
        ability: "You start knowing that 1 of 2 players is a particular Townsfolk.",
        first_night: true
    },
    Librarian: "Librarian" => {
        team: Townsfolk,
        ability: "You start knowing that 1 of 2 players is a particular Outsider, or that zero Outsiders are in play.",
        first_night: true
    },
    Investigator: "Investigator" => {
        team: Townsfolk,
        ability: "You start knowing that 1 of 2 players is a particular Minion.",
        first_night: true
    },
    Chef: "Chef" => {
        team: Townsfolk,
        ability: "You start knowing how many pairs of evil players there are.",
        first_night: true
    },
    Empath: "Empath" => {
        team: Townsfolk,
        ability: "Each night, you learn how many of your 2 alive neighbours are evil.",
        all_nights: true
    },
    FortuneTeller: "Fortune Teller" => {
        team: Townsfolk,
        ability: "Each night, choose 2 players: you learn if either is a Demon. There is a good player that registers as a Demon to you.",
        all_nights: true
    },
    Undertaker: "Undertaker" => {
        team: Townsfolk,
        ability: "Each night*, you learn which character died by execution today.",
        other_nights: true
    },
    Monk: "Monk" => {
        team: Townsfolk,
        ability: "Each night*, choose a player (not yourself): they are safe from the Demon tonight.",
        other_nights: true
    },
    Ravenkeeper: "Ravenkeeper" => {
        team: Townsfolk,
        ability: "If you die at night, you are woken to choose a player: you learn their character.",
        other_nights: true
    },
    Virgin: "Virgin" => {
        team: Townsfolk,
        ability: "The 1st time you are nominated, if the nominator is a Townsfolk, they are executed immediately."
    },
    Slayer: "Slayer" => {
        team: Townsfolk,
        ability: "Once per game, during the day, publicly choose a player: if they are the Demon, they die."
    },
    Soldier: "Soldier" => {
        team: Townsfolk,
        ability: "You are safe from the Demon."
    },
    Mayor: "Mayor" => {
        team: Townsfolk,
        ability: "If only 3 players live & no execution occurs, your team wins. If you die at night, another player might die instead."
    },

    // Outsiders
    Butler: "Butler" => {
        team: Outsider,
        ability: "Each night, choose a player (not yourself): tomorrow, you may only vote if they are voting too.",
        all_nights: true
    },
    Drunk: "Drunk" => {
        team: Outsider,
        ability: "You do not know you are the Drunk. You think you are a Townsfolk character, but you are not."
    },
    Recluse: "Recluse" => {
        team: Outsider,
        ability: "You might register as evil & as a Minion or Demon, even if dead."
    },
    Saint: "Saint" => {
        team: Outsider,
        ability: "If you die by execution, your team loses."
    },

    // Minions
    Baron: "Baron" => {
        team: Minion,
        ability: "There are extra Outsiders in play. [+2 Outsiders]",
        setup: SetupModifier::AdjustCounts { remove_townsfolk: 2, add_outsiders: 2 }
    },
    Poisoner: "Poisoner" => {
        team: Minion,
        ability: "Each night, choose a player: they are poisoned tonight and tomorrow day.",
        other_nights: true
    },
    ScarletWoman: "Scarlet Woman" => {
        team: Minion,
        ability: "If there are 5 or more players alive & the Demon dies, you become the Demon."
    },
    Spy: "Spy" => {
        team: Minion,
        ability: "Each night, you see the Grimoire. You might register as good & as a Townsfolk or Outsider, even if dead.",
        all_nights: true
    },

    // Demon
    Imp: "Imp" => {
        team: Demon,
        ability: "Each night*, choose a player: they die. If you kill yourself this way, a Minion becomes the Imp.",
        other_nights: true
    },

    // Experimental characters
    VillageIdiot: "Village Idiot" => {
        team: Townsfolk,
        ability: "Each night, choose a player: you learn their alignment. [+0 to +2 Village Idiots. 1 of the extras is drunk]",
        all_nights: true
    },
}

// Script: a named collection of roles
#[derive(Debug, Clone)]
struct Script {
    title: String,
    roles: Vec<Role>,
}

impl Script {
    fn trouble_brewing() -> Self {
        let role_names = vec![
            "Washerwoman", "Librarian", "Investigator", "Chef", "Empath", "Fortune Teller",
            "Undertaker", "Monk", "Ravenkeeper", "Virgin", "Slayer", "Soldier", "Mayor",
            "Butler", "Drunk", "Recluse", "Saint",
            "Poisoner", "Spy", "Scarlet Woman", "Baron",
            "Imp",
        ];

        let mut roles = Vec::new();
        for name in role_names {
            for role in Role::all() {
                if role.name() == name {
                    roles.push(*role);
                    break;
                }
            }
        }

        Script {
            title: "Trouble Brewing".to_string(),
            roles,
        }
    }

    fn from_name(name: &str) -> Option<Self> {
        match name.to_lowercase().replace(&[' ', '-', '_'][..], "").as_str() {
            "troublebrewing" | "tb" => Some(Script::trouble_brewing()),
            _ => None,
        }
    }
}

// Bag legality problem: Given player count and selected roles,
// is the resulting distribution legal?
#[derive(Debug, Clone)]
struct RoleDistribution {
    townsfolk: u8,
    outsider: u8,
    minion: u8,
    demon: u8,
}

impl RoleDistribution {
    #[allow(dead_code)]
    fn total(&self) -> u8 {
        self.townsfolk + self.outsider + self.minion + self.demon
    }

    // Standard BotC distribution for N players (before role modifiers)
    fn base_setup(player_count: u8) -> Self {
        match player_count {
            // DEBUG: Allow tiny bags for testing
            1 => RoleDistribution {
                townsfolk: 0,
                outsider: 0,
                minion: 0,
                demon: 1,
            },
            2 => RoleDistribution {
                townsfolk: 1,
                outsider: 0,
                minion: 0,
                demon: 1,
            },
            3 => RoleDistribution {
                townsfolk: 2,
                outsider: 0,
                minion: 0,
                demon: 1,
            },
            4 => RoleDistribution {
                townsfolk: 2,
                outsider: 0,
                minion: 1,
                demon: 1,
            },

            // Standard BotC
            5 => RoleDistribution {
                townsfolk: 3,
                outsider: 0,
                minion: 1,
                demon: 1,
            },
            6 => RoleDistribution {
                townsfolk: 3,
                outsider: 1,
                minion: 1,
                demon: 1,
            },
            n @ 7..=15 => {
                let past_four = n - 4;
                let minion = past_four / 3;
                let outsider = past_four % 3;
                let townsfolk = 3 + (minion * 2);
                RoleDistribution {
                    townsfolk,
                    outsider,
                    minion,
                    demon: 1,
                }
            }
            _ => panic!("Invalid player count: {}", player_count),
        }
    }
}

// Variable manager for bag legality encoding
struct BagVariables {
    instance: SatInstance<BasicVarManager>,

    // role_present[role] - is this role in the game?
    role_present: std::collections::HashMap<Role, rustsat::types::Lit>,

    // final_townsfolk[n] - true if exactly n townsfolk in play
    final_townsfolk: Vec<rustsat::types::Lit>,
    final_outsider: Vec<rustsat::types::Lit>,
    final_minion: Vec<rustsat::types::Lit>,
    final_demon: Vec<rustsat::types::Lit>,

    // physical_townsfolk[n] - true if exactly n townsfolk tokens in physical bag
    physical_townsfolk: Vec<rustsat::types::Lit>,
    physical_outsider: Vec<rustsat::types::Lit>,
    physical_minion: Vec<rustsat::types::Lit>,
    physical_demon: Vec<rustsat::types::Lit>,
}

impl BagVariables {
    fn new(max_count: usize) -> Self {
        let mut instance = SatInstance::new();
        let mut role_present = std::collections::HashMap::new();

        // Create variables for each role
        for role in Role::all() {
            let lit = instance.new_lit();
            role_present.insert(*role, lit);
        }

        // Create count variables (0..=max_count for each type)
        let mut final_townsfolk = Vec::new();
        let mut final_outsider = Vec::new();
        let mut final_minion = Vec::new();
        let mut final_demon = Vec::new();

        let mut physical_townsfolk = Vec::new();
        let mut physical_outsider = Vec::new();
        let mut physical_minion = Vec::new();
        let mut physical_demon = Vec::new();

        for _ in 0..=max_count {
            final_townsfolk.push(instance.new_lit());
            final_outsider.push(instance.new_lit());
            final_minion.push(instance.new_lit());
            final_demon.push(instance.new_lit());

            physical_townsfolk.push(instance.new_lit());
            physical_outsider.push(instance.new_lit());
            physical_minion.push(instance.new_lit());
            physical_demon.push(instance.new_lit());
        }

        BagVariables {
            instance,
            role_present,
            final_townsfolk,
            final_outsider,
            final_minion,
            final_demon,
            physical_townsfolk,
            physical_outsider,
            physical_minion,
            physical_demon,
        }
    }

    fn get_count_vars(&self, team: Team) -> &[rustsat::types::Lit] {
        match team {
            Team::Townsfolk => &self.final_townsfolk,
            Team::Outsider => &self.final_outsider,
            Team::Minion => &self.final_minion,
            Team::Demon => &self.final_demon,
        }
    }

    fn get_physical_count_vars(&self, team: Team) -> &[rustsat::types::Lit] {
        match team {
            Team::Townsfolk => &self.physical_townsfolk,
            Team::Outsider => &self.physical_outsider,
            Team::Minion => &self.physical_minion,
            Team::Demon => &self.physical_demon,
        }
    }

    // Extract which roles are present from a SAT model
    #[allow(dead_code)]
    fn extract_present_roles<S: Solve>(&self, solver: &S) -> Result<Vec<Role>, String> {
        let mut present = Vec::new();
        for role in Role::all() {
            let lit = self.role_present[role];
            match solver.lit_val(lit) {
                Ok(TernaryVal::True) => present.push(*role),
                Ok(TernaryVal::False) => {}
                Ok(TernaryVal::DontCare) => {
                    // Shouldn't happen if we're extracting from a SAT solution
                    return Err(format!(
                        "Variable for {} is unassigned in model",
                        role.name()
                    ));
                }
                Err(e) => return Err(format!("Failed to get value for {}: {}", role.name(), e)),
            }
        }
        Ok(present)
    }
}

fn encode_exactly_one(instance: &mut SatInstance<BasicVarManager>, lits: &[rustsat::types::Lit]) {
    // At least one must be true
    let clause: Clause = lits.iter().copied().collect();
    instance.add_clause(clause);

    // At most one is true (pairwise mutex)
    for i in 0..lits.len() {
        for j in i + 1..lits.len() {
            instance.add_binary(!lits[i], !lits[j]);
        }
    }
}

/// Encode "at most n of these literals can be true"
/// Uses pairwise exclusion for small n, or more efficient encoding for larger n
#[allow(dead_code)]
fn encode_at_most_n(
    instance: &mut SatInstance<BasicVarManager>,
    lits: &[rustsat::types::Lit],
    n: usize,
) {
    if n == 0 {
        // None can be true
        for &lit in lits {
            instance.add_unit(!lit);
        }
    } else if n >= lits.len() {
        // Constraint is trivially satisfied
        return;
    } else if n == 1 {
        // At most one: use pairwise exclusion
        for i in 0..lits.len() {
            for j in i + 1..lits.len() {
                instance.add_binary(!lits[i], !lits[j]);
            }
        }
    } else {
        // For n > 1, we need a more sophisticated encoding
        // Use the complement: "at most n" = "at least (len - n) are false"
        // Which is "at most n are true"
        // For simplicity, we'll use pairwise "at most n+1 choose 2" constraints
        // This says: among any (n+1) literals, at least one must be false

        // Generate all (n+1)-combinations and add "at least one is false" constraint
        let mut combinations = Vec::new();
        generate_combinations(lits, n + 1, &mut combinations);

        for combo in combinations {
            // At least one in this combo must be false
            let clause: Clause = combo.iter().map(|&lit| !lit).collect();
            instance.add_clause(clause);
        }
    }
}

/// Generate all k-combinations of elements from the slice
fn generate_combinations<T: Copy>(
    elements: &[T],
    k: usize,
    result: &mut Vec<Vec<T>>,
) {
    if k == 0 || k > elements.len() {
        return;
    }

    let mut current = Vec::with_capacity(k);
    generate_combinations_helper(elements, k, 0, &mut current, result);
}

fn generate_combinations_helper<T: Copy>(
    elements: &[T],
    k: usize,
    start: usize,
    current: &mut Vec<T>,
    result: &mut Vec<Vec<T>>,
) {
    if current.len() == k {
        result.push(current.clone());
        return;
    }

    for i in start..elements.len() {
        current.push(elements[i]);
        generate_combinations_helper(elements, k, i + 1, current, result);
        current.pop();
    }
}

// Encode: exactly n of target_vars are true (unconditional)
// Use pairwise at-most-one for small cases, fall back to sequential for larger
#[allow(dead_code)]
fn encode_exactly_n(
    instance: &mut SatInstance<BasicVarManager>,
    target_vars: &[rustsat::types::Lit],
    n: usize,
) {
    let num_vars = target_vars.len();

    if n > num_vars {
        // Impossible - add a contradiction
        let false_lit = instance.new_lit();
        instance.add_unit(false_lit);
        instance.add_unit(!false_lit);
        return;
    }

    if n == 0 {
        // All must be false
        for &var in target_vars {
            instance.add_unit(!var);
        }
        return;
    }

    if n == num_vars {
        // All must be true
        for &var in target_vars {
            instance.add_unit(var);
        }
        return;
    }

    // Use simple pairwise encoding for "at-most-one" case
    if n == 1 {
        // At least one
        let clause: Clause = target_vars.iter().copied().collect();
        instance.add_clause(clause);

        // At most one (pairwise)
        for i in 0..target_vars.len() {
            for j in i + 1..target_vars.len() {
                instance.add_binary(!target_vars[i], !target_vars[j]);
            }
        }
        return;
    }

    // For larger n, use unconditional sequential counter
    // Build it directly instead of using a condition variable

    // Sequential counter: s[i][k] means "at least k of first i variables are true"
    let mut s: Vec<Vec<rustsat::types::Lit>> = Vec::new();
    for _ in 0..=num_vars {
        let mut row = Vec::new();
        for _ in 0..=n {
            row.push(instance.new_lit());
        }
        s.push(row);
    }

    // Base case
    instance.add_unit(s[0][0]);
    for k in 1..=n {
        instance.add_unit(!s[0][k]);
    }

    // Recursive case
    for i in 1..=num_vars {
        let target = target_vars[i - 1];

        for k in 0..=n {
            // s[i][k] => s[i-1][k] OR s[i-1][k-1]
            if k == 0 {
                instance.add_binary(!s[i][k], s[i - 1][k]);
            } else {
                instance.add_clause(
                    vec![!s[i][k], s[i - 1][k], s[i - 1][k - 1]]
                        .into_iter()
                        .collect(),
                );
            }

            // s[i-1][k] AND NOT target => s[i][k]
            instance.add_clause(vec![!s[i - 1][k], target, s[i][k]].into_iter().collect());

            // s[i-1][k-1] AND target => s[i][k]
            if k > 0 {
                instance.add_clause(
                    vec![!s[i - 1][k - 1], !target, s[i][k]]
                        .into_iter()
                        .collect(),
                );
            }
        }
    }

    // At least n
    instance.add_unit(s[num_vars][n]);

    // At most n
    if n < num_vars {
        let mut s_n_plus_1: Vec<rustsat::types::Lit> = Vec::new();
        for _ in 0..=num_vars {
            s_n_plus_1.push(instance.new_lit());
        }

        instance.add_unit(!s_n_plus_1[0]);

        for i in 1..=num_vars {
            let target = target_vars[i - 1];

            instance.add_clause(
                vec![!s_n_plus_1[i], s_n_plus_1[i - 1], s[i - 1][n]]
                    .into_iter()
                    .collect(),
            );
            instance.add_clause(
                vec![!s_n_plus_1[i - 1], target, s_n_plus_1[i]]
                    .into_iter()
                    .collect(),
            );
            instance.add_clause(
                vec![!s[i - 1][n], !target, s_n_plus_1[i]]
                    .into_iter()
                    .collect(),
            );
        }

        instance.add_unit(!s_n_plus_1[num_vars]);
    }
}

// Naive encoding: exactly n of target_vars are true
// WARNING: Generates O(C(m,n)) clauses where m = |target_vars|
#[allow(dead_code)]
fn encode_exactly_n_naive(
    instance: &mut SatInstance<BasicVarManager>,
    target_vars: &[rustsat::types::Lit],
    n: usize,
) {
    use std::collections::VecDeque;

    let m = target_vars.len();

    // At-most-n: every (n+1)-subset must have at least one false
    let mut stack = VecDeque::new();
    stack.push_back((0, Vec::new()));

    while let Some((start, current)) = stack.pop_back() {
        if current.len() == n + 1 {
            // Add clause: at least one of these (n+1) must be false
            let lits: Vec<rustsat::types::Lit> =
                current.iter().map(|&i: &usize| !target_vars[i]).collect();
            let clause: Clause = lits.into_iter().collect();
            instance.add_clause(clause);
            continue;
        }

        if start >= m || m - start < (n + 1 - current.len()) {
            continue;
        }

        // Try including start
        let mut with_start = current.clone();
        with_start.push(start);
        stack.push_back((start + 1, with_start));

        // Try not including start
        stack.push_back((start + 1, current));
    }

    // At-least-n: every (m-n+1)-subset must have at least one true
    let subset_size = m - n + 1;
    let mut stack = VecDeque::new();
    stack.push_back((0, Vec::new()));

    while let Some((start, current)) = stack.pop_back() {
        if current.len() == subset_size {
            // Add clause: at least one of these must be true
            let lits: Vec<rustsat::types::Lit> =
                current.iter().map(|&i: &usize| target_vars[i]).collect();
            let clause: Clause = lits.into_iter().collect();
            instance.add_clause(clause);
            continue;
        }

        if start >= m || m - start < (subset_size - current.len()) {
            continue;
        }

        // Try including start
        let mut with_start = current.clone();
        with_start.push(start);
        stack.push_back((start + 1, with_start));

        // Try not including start
        stack.push_back((start + 1, current));
    }
}

// Encode: condition => exactly n of target_vars are true
// Uses sequential counter encoding: s[i][k] = "at least k of first i vars are true"
fn encode_conditional_exactly_n(
    instance: &mut SatInstance<BasicVarManager>,
    condition: rustsat::types::Lit,
    target_vars: &[rustsat::types::Lit],
    n: usize,
) {
    let num_vars = target_vars.len();

    if num_vars < n {
        // Impossible: need more than available
        // Add: NOT condition
        instance.add_unit(!condition);
        return;
    }

    if n == 0 {
        // All targets must be false
        for &var in target_vars {
            instance.add_binary(!condition, !var);
        }
        return;
    }

    if n == num_vars {
        // All targets must be true
        for &var in target_vars {
            instance.add_binary(!condition, var);
        }
        return;
    }

    // Sequential counter: s[i][k] means "at least k of first i variables are true"
    // Create auxiliary variables s[i][k] for i in 0..=num_vars, k in 0..=n
    let mut s: Vec<Vec<rustsat::types::Lit>> = Vec::new();
    for _ in 0..=num_vars {
        let mut row = Vec::new();
        for _ in 0..=n {
            row.push(instance.new_lit());
        }
        s.push(row);
    }

    // Base case: s[0][0] = true (0 of first 0 vars => true)
    instance.add_unit(s[0][0]);

    // Base case: s[0][k] = false for k > 0 (can't have k>0 from 0 vars)
    for k in 1..=n {
        instance.add_unit(!s[0][k]);
    }

    // Recursive case: s[i][k] is true iff:
    //   (s[i-1][k] AND NOT target[i-1]) OR (s[i-1][k-1] AND target[i-1])
    // Encoding:
    //   s[i][k] => s[i-1][k] OR s[i-1][k-1]
    //   s[i-1][k] AND NOT target[i-1] => s[i][k]
    //   s[i-1][k-1] AND target[i-1] => s[i][k]

    for i in 1..=num_vars {
        let target = target_vars[i - 1];

        for k in 0..=n {
            // s[i][k] => s[i-1][k] OR s[i-1][k-1]
            if k == 0 {
                instance.add_binary(!s[i][k], s[i - 1][k]);
            } else {
                instance.add_clause(
                    vec![!s[i][k], s[i - 1][k], s[i - 1][k - 1]]
                        .into_iter()
                        .collect(),
                );
            }

            // s[i-1][k] AND NOT target => s[i][k]
            instance.add_clause(vec![!s[i - 1][k], target, s[i][k]].into_iter().collect());

            // s[i-1][k-1] AND target => s[i][k]
            if k > 0 {
                instance.add_clause(
                    vec![!s[i - 1][k - 1], !target, s[i][k]]
                        .into_iter()
                        .collect(),
                );
            }
        }
    }

    // Final constraint: condition => s[num_vars][n] (at least n)
    instance.add_binary(!condition, s[num_vars][n]);

    // Final constraint: condition => NOT s[num_vars][n+1] (at most n)
    // Since we only track up to n, this means we ensure exactly n
    // We need: if condition, then we have exactly n (not more)
    // Add: NOT target[i] for all ways to get to n+1
    // Simpler: condition AND s[num_vars][n] => NOT (any more can be true beyond n)

    // Actually, we need to ensure "not more than n"
    // The sequential counter s[num_vars][n] = "at least n"
    // We also need "at most n" = "NOT at least n+1"
    // Let's add constraints that if we have n, we can't add more

    // Better approach: s[i][n] AND target[i+1] => false when i = num_vars
    // This says: if we already have n from first num_vars, we can't have any more
    // But we've already consumed all vars...

    // Actually, the standard sequential encoding for "exactly n" is:
    // - At least n: s[num_vars][n]
    // - At most n: NOT s[num_vars][n+1] (but we only go up to n)

    // We need to extend to n+1 to encode "at most n"
    if n < num_vars {
        let mut s_n_plus_1: Vec<rustsat::types::Lit> = Vec::new();
        for _ in 0..=num_vars {
            s_n_plus_1.push(instance.new_lit());
        }

        // s[0][n+1] = false
        instance.add_unit(!s_n_plus_1[0]);

        // Build s[i][n+1] same way
        for i in 1..=num_vars {
            let target = target_vars[i - 1];

            // s[i][n+1] => s[i-1][n+1] OR s[i-1][n]
            instance.add_clause(
                vec![!s_n_plus_1[i], s_n_plus_1[i - 1], s[i - 1][n]]
                    .into_iter()
                    .collect(),
            );

            // s[i-1][n+1] AND NOT target => s[i][n+1]
            instance.add_clause(
                vec![!s_n_plus_1[i - 1], target, s_n_plus_1[i]]
                    .into_iter()
                    .collect(),
            );

            // s[i-1][n] AND target => s[i][n+1]
            instance.add_clause(
                vec![!s[i - 1][n], !target, s_n_plus_1[i]]
                    .into_iter()
                    .collect(),
            );
        }

        // condition => NOT s[num_vars][n+1]
        instance.add_binary(!condition, !s_n_plus_1[num_vars]);
    }
}

#[allow(dead_code)]
fn encode_bag_legality(player_count: u8, selected_roles: &[Role]) -> BagVariables {
    let mut vars = BagVariables::new(player_count as usize);

    // 1. Exactly one count per type (both in-play and physical)
    encode_exactly_one(&mut vars.instance, &vars.final_townsfolk);
    encode_exactly_one(&mut vars.instance, &vars.final_outsider);
    encode_exactly_one(&mut vars.instance, &vars.final_minion);
    encode_exactly_one(&mut vars.instance, &vars.final_demon);

    encode_exactly_one(&mut vars.instance, &vars.physical_townsfolk);
    encode_exactly_one(&mut vars.instance, &vars.physical_outsider);
    encode_exactly_one(&mut vars.instance, &vars.physical_minion);
    encode_exactly_one(&mut vars.instance, &vars.physical_demon);

    // 2. Create slot variables for each role position
    let mut slot_role_vars: Vec<std::collections::HashMap<Role, rustsat::types::Lit>> = Vec::new();
    for _ in 0..selected_roles.len() {
        let mut slot_map = std::collections::HashMap::new();
        for role in Role::all() {
            slot_map.insert(*role, vars.instance.new_lit());
        }
        slot_role_vars.push(slot_map);
    }

    // 3. Each slot must contain exactly one role
    for slot_map in slot_role_vars.iter() {
        let slot_lits: Vec<rustsat::types::Lit> = Role::all().iter().map(|r| slot_map[r]).collect();
        encode_exactly_one(&mut vars.instance, &slot_lits);
    }

    // 4. Link slot variables to role_present
    for role in Role::all() {
        let slots_with_this_role: Vec<rustsat::types::Lit> = slot_role_vars
            .iter()
            .map(|slot_map| slot_map[role])
            .collect();

        let role_present_lit = vars.role_present[role];

        // Forward: role_present => at least one slot has it
        let mut clause: Vec<rustsat::types::Lit> = vec![!role_present_lit];
        clause.extend(slots_with_this_role.iter().copied());
        vars.instance.add_clause(clause.into_iter().collect());

        // Backward: if any slot has it => role_present
        for &slot_lit in &slots_with_this_role {
            vars.instance.add_binary(!slot_lit, role_present_lit);
        }
    }

    // 5. Fix each slot to its specific role
    for (slot_idx, role) in selected_roles.iter().enumerate() {
        let slot_lit = slot_role_vars[slot_idx][role];
        vars.instance.add_unit(slot_lit);
    }

    // 6. Base distribution and apply modifiers
    let base = RoleDistribution::base_setup(player_count);
    println!(
        "Base setup for {} players: T={}, O={}, M={}, D={}",
        player_count, base.townsfolk, base.outsider, base.minion, base.demon
    );

    // Calculate final distribution after applying modifiers
    let mut final_dist = base.clone();
    for role in selected_roles {
        if let Some(modifier) = role.setup_modifier() {
            match modifier {
                SetupModifier::AdjustCounts {
                    remove_townsfolk,
                    add_outsiders,
                } => {
                    println!(
                        "  {} modifies: -{}T, +{}O",
                        role.name(),
                        remove_townsfolk,
                        add_outsiders
                    );
                    final_dist.townsfolk = final_dist.townsfolk.saturating_sub(remove_townsfolk);
                    final_dist.outsider = final_dist.outsider.saturating_add(add_outsiders);
                }
            }
        }
    }

    println!(
        "Final distribution: T={}, O={}, M={}, D={}",
        final_dist.townsfolk, final_dist.outsider, final_dist.minion, final_dist.demon
    );

    // Assert final distribution for in-play
    vars.instance
        .add_unit(vars.final_townsfolk[final_dist.townsfolk as usize]);
    vars.instance
        .add_unit(vars.final_outsider[final_dist.outsider as usize]);
    vars.instance
        .add_unit(vars.final_minion[final_dist.minion as usize]);
    vars.instance
        .add_unit(vars.final_demon[final_dist.demon as usize]);

    // 7. Role type matching: count slot assignments instead of role presence
    encode_role_type_matching(&mut vars, Team::Townsfolk, &slot_role_vars);
    encode_role_type_matching(&mut vars, Team::Outsider, &slot_role_vars);
    encode_role_type_matching(&mut vars, Team::Minion, &slot_role_vars);
    encode_role_type_matching(&mut vars, Team::Demon, &slot_role_vars);

    // 8. Physical bag substitution (Drunk)
    encode_physical_bag_constraints(&mut vars);

    vars
}

// Type alias for complex return type used in encoding functions
type EncodingResult = (
    BagVariables,
    Vec<(String, Option<Team>)>,
    Vec<std::collections::HashMap<Role, rustsat::types::Lit>>,
);

fn encode_bag_spec_legality_with_script(
    player_count: u8,
    specs: &[RoleSpec],
    script: Option<&Script>,
) -> EncodingResult {
    let mut vars = BagVariables::new(player_count as usize);
    let mut placeholders = Vec::new();

    // Determine which roles are available based on script
    let available_roles: &[Role] = if let Some(script) = script {
        &script.roles
    } else {
        Role::all()
    };

    // NEW: slot_role[slot_idx][role] = "slot i is filled by role r"
    // Only create variables for available roles (from script or all roles)
    let mut slot_role_vars: Vec<std::collections::HashMap<Role, rustsat::types::Lit>> = Vec::new();

    for _ in 0..specs.len() {
        let mut slot_map = std::collections::HashMap::new();
        for role in available_roles {
            slot_map.insert(*role, vars.instance.new_lit());
        }
        slot_role_vars.push(slot_map);
    }

    // 1. Each slot must contain exactly one role
    for slot_map in &slot_role_vars {
        let slot_lits: Vec<rustsat::types::Lit> = available_roles.iter().map(|r| slot_map[r]).collect();
        encode_exactly_one(&mut vars.instance, &slot_lits);
    }

    // 2. Link slot variables to role_present: role_present[r] <=> (exists slot with role r)
    for role in available_roles {
        let slots_with_this_role: Vec<rustsat::types::Lit> = slot_role_vars
            .iter()
            .map(|slot_map| slot_map[role])
            .collect();

        // role_present[r] <=> at-least-one slot has role r
        let role_present_lit = vars.role_present[role];

        // Forward: role_present => at least one slot has it
        let mut clause: Vec<rustsat::types::Lit> = vec![!role_present_lit];
        clause.extend(slots_with_this_role.iter().copied());
        vars.instance.add_clause(clause.into_iter().collect());

        // Backward: if any slot has it => role_present
        for &slot_lit in &slots_with_this_role {
            vars.instance.add_binary(!slot_lit, role_present_lit);
        }

        // At most max_count slots can have this role
        // Standard roles: max_count = 1 (prevents duplicates like "Mayor, Mayor, Imp")
        // Experimental roles: max_count > 1 (e.g., Village Idiot can appear up to 3 times)
        let max_count = role.max_count() as usize;
        encode_at_most_n(&mut vars.instance, &slots_with_this_role, max_count);
    }

    // 3. Exactly one count per type (both in-play and physical)
    encode_exactly_one(&mut vars.instance, &vars.final_townsfolk);
    encode_exactly_one(&mut vars.instance, &vars.final_outsider);
    encode_exactly_one(&mut vars.instance, &vars.final_minion);
    encode_exactly_one(&mut vars.instance, &vars.final_demon);

    encode_exactly_one(&mut vars.instance, &vars.physical_townsfolk);
    encode_exactly_one(&mut vars.instance, &vars.physical_outsider);
    encode_exactly_one(&mut vars.instance, &vars.physical_minion);
    encode_exactly_one(&mut vars.instance, &vars.physical_demon);

    // 4. Assert known roles in their slots, leave placeholders free
    for (slot_idx, spec) in specs.iter().enumerate() {
        match spec {
            RoleSpec::Known(role) => {
                // This slot must contain this specific role
                let slot_lit = slot_role_vars[slot_idx][role];
                vars.instance.add_unit(slot_lit);
            }
            RoleSpec::Placeholder {
                name,
                team_constraint,
            } => {
                // Apply team constraint if present
                if let Some(team) = team_constraint {
                    // This slot must contain a role of this team
                    for role in available_roles {
                        if role.team() != *team {
                            // Disallow this role in this slot
                            vars.instance.add_unit(!slot_role_vars[slot_idx][role]);
                        }
                    }
                }
                placeholders.push((name.clone(), *team_constraint));
            }
        }
    }

    // Note: We don't need an explicit "exactly N total roles" constraint anymore!
    // The slot variables implicitly enforce this: N slots × exactly-one role per slot = N roles total

    // 3. Base distribution and handle role modifiers
    let base = RoleDistribution::base_setup(player_count);

    // With placeholders, modifiers like Baron might or might not be present
    // We need conditional encoding: "IF Baron THEN modified distribution, ELSE base distribution"

    // Check if any modifier roles are known vs potential placeholders
    let known_roles: Vec<Role> = specs
        .iter()
        .filter_map(|s| match s {
            RoleSpec::Known(r) => Some(*r),
            _ => None,
        })
        .collect();

    // Apply known modifiers to get baseline
    let mut final_dist_without_unknown_modifiers = base.clone();
    for role in &known_roles {
        if let Some(modifier) = role.setup_modifier() {
            match modifier {
                SetupModifier::AdjustCounts {
                    remove_townsfolk,
                    add_outsiders,
                } => {
                    final_dist_without_unknown_modifiers.townsfolk =
                        final_dist_without_unknown_modifiers
                            .townsfolk
                            .saturating_sub(remove_townsfolk);
                    final_dist_without_unknown_modifiers.outsider =
                        final_dist_without_unknown_modifiers
                            .outsider
                            .saturating_add(add_outsiders);
                }
            }
        }
    }

    if placeholders.is_empty() {
        // No placeholders - assert exact distribution
        vars.instance.add_unit(
            vars.final_townsfolk[final_dist_without_unknown_modifiers.townsfolk as usize],
        );
        vars.instance
            .add_unit(vars.final_outsider[final_dist_without_unknown_modifiers.outsider as usize]);
        vars.instance
            .add_unit(vars.final_minion[final_dist_without_unknown_modifiers.minion as usize]);
        vars.instance
            .add_unit(vars.final_demon[final_dist_without_unknown_modifiers.demon as usize]);
    } else {
        // Placeholders exist - need to handle potential role modifiers conditionally
        // Collect all roles with modifiers that could be placeholders
        let modifier_roles: Vec<(Role, SetupModifier)> = Role::all()
            .iter()
            .filter(|r| !known_roles.contains(r))
            .filter_map(|r| r.setup_modifier().map(|m| (*r, m)))
            .collect();

        if modifier_roles.is_empty() {
            // No potential modifier roles - use base distribution
            let base_dist = final_dist_without_unknown_modifiers;
            vars.instance
                .add_unit(vars.final_townsfolk[base_dist.townsfolk as usize]);
            vars.instance
                .add_unit(vars.final_outsider[base_dist.outsider as usize]);
            vars.instance
                .add_unit(vars.final_minion[base_dist.minion as usize]);
            vars.instance
                .add_unit(vars.final_demon[base_dist.demon as usize]);
        } else {
            // At least one modifier role could be a placeholder
            // Strategy: Assert that distribution must be one of the valid values
            // For Trouble Brewing: either base (3T/0O/1M/1D) or Baron-modified (1T/2O/1M/1D)

            let base_dist = final_dist_without_unknown_modifiers;

            // For each modifier role, encode: role_present <=> modified_distribution
            for (role, modifier) in &modifier_roles {
                match modifier {
                    SetupModifier::AdjustCounts {
                        remove_townsfolk,
                        add_outsiders,
                    } => {
                        let modified_t = base_dist.townsfolk.saturating_sub(*remove_townsfolk);
                        let modified_o = base_dist.outsider.saturating_add(*add_outsiders);

                        let role_lit = vars.role_present[role];

                        // Forward: role_present => modified distribution
                        vars.instance
                            .add_binary(!role_lit, vars.final_townsfolk[modified_t as usize]);
                        vars.instance
                            .add_binary(!role_lit, vars.final_outsider[modified_o as usize]);
                        vars.instance
                            .add_binary(!role_lit, vars.final_minion[base_dist.minion as usize]);
                        vars.instance
                            .add_binary(!role_lit, vars.final_demon[base_dist.demon as usize]);

                        // Note: We don't encode the backward direction (modified_dist => role) because:
                        // 1. Multiple modifier roles could theoretically produce the same distribution
                        // 2. The forward direction + "no modifiers => base" constraint is sufficient
                        //    for Trouble Brewing (only Baron has modifiers)
                    }
                }
            }

            // Encode: IF all modifier roles absent THEN base distribution
            // (!baron AND !...) => base_dist
            // This is: baron OR ... OR base_townsfolk[base.t]
            let mut clause: Vec<rustsat::types::Lit> = modifier_roles
                .iter()
                .map(|(r, _)| vars.role_present[r])
                .collect();
            clause.push(vars.final_townsfolk[base_dist.townsfolk as usize]);
            vars.instance.add_clause(clause.into_iter().collect());

            let mut clause: Vec<rustsat::types::Lit> = modifier_roles
                .iter()
                .map(|(r, _)| vars.role_present[r])
                .collect();
            clause.push(vars.final_outsider[base_dist.outsider as usize]);
            vars.instance.add_clause(clause.into_iter().collect());

            let mut clause: Vec<rustsat::types::Lit> = modifier_roles
                .iter()
                .map(|(r, _)| vars.role_present[r])
                .collect();
            clause.push(vars.final_minion[base_dist.minion as usize]);
            vars.instance.add_clause(clause.into_iter().collect());

            let mut clause: Vec<rustsat::types::Lit> = modifier_roles
                .iter()
                .map(|(r, _)| vars.role_present[r])
                .collect();
            clause.push(vars.final_demon[base_dist.demon as usize]);
            vars.instance.add_clause(clause.into_iter().collect());
        }
    }

    // 4. Role type matching: if final_townsfolk[k], then exactly k slots have townsfolk roles
    encode_role_type_matching(&mut vars, Team::Townsfolk, &slot_role_vars);
    encode_role_type_matching(&mut vars, Team::Outsider, &slot_role_vars);
    encode_role_type_matching(&mut vars, Team::Minion, &slot_role_vars);
    encode_role_type_matching(&mut vars, Team::Demon, &slot_role_vars);

    // 5. Physical bag substitution (Drunk)
    encode_physical_bag_constraints(&mut vars);

    (vars, placeholders, slot_role_vars)
}


fn encode_bag_spec_legality_chain_with_script(
    player_count: u8,
    specs: &[RoleSpec],
    script: Option<&Script>,
) -> EncodingResult {
    let mut vars = BagVariables::new(player_count as usize);

    // Determine which roles are available based on script
    let available_roles: &[Role] = if let Some(script) = script {
        &script.roles
    } else {
        Role::all()
    };

    // 1. Exactly one count per type (both in-play and physical)
    encode_exactly_one(&mut vars.instance, &vars.final_townsfolk);
    encode_exactly_one(&mut vars.instance, &vars.final_outsider);
    encode_exactly_one(&mut vars.instance, &vars.final_minion);
    encode_exactly_one(&mut vars.instance, &vars.final_demon);

    encode_exactly_one(&mut vars.instance, &vars.physical_townsfolk);
    encode_exactly_one(&mut vars.instance, &vars.physical_outsider);
    encode_exactly_one(&mut vars.instance, &vars.physical_minion);
    encode_exactly_one(&mut vars.instance, &vars.physical_demon);

    // 2. Create slot variables (only for available roles)
    let mut slot_role_vars: Vec<std::collections::HashMap<Role, rustsat::types::Lit>> = Vec::new();
    for _ in 0..specs.len() {
        let mut slot_map = std::collections::HashMap::new();
        for role in available_roles {
            slot_map.insert(*role, vars.instance.new_lit());
        }
        slot_role_vars.push(slot_map);
    }

    // 3. Each slot must contain exactly one role
    for slot_map in slot_role_vars.iter() {
        let slot_lits: Vec<rustsat::types::Lit> = available_roles.iter().map(|r| slot_map[r]).collect();
        encode_exactly_one(&mut vars.instance, &slot_lits);
    }

    // 4. Link slot variables to role_present
    for role in available_roles {
        let slots_with_this_role: Vec<rustsat::types::Lit> = slot_role_vars
            .iter()
            .map(|slot_map| slot_map[role])
            .collect();

        let role_present_lit = vars.role_present[role];

        // Forward: role_present => at least one slot has it
        let mut clause: Vec<rustsat::types::Lit> = vec![!role_present_lit];
        clause.extend(slots_with_this_role.iter().copied());
        vars.instance.add_clause(clause.into_iter().collect());

        // Backward: if any slot has it => role_present
        for &slot_lit in &slots_with_this_role {
            vars.instance.add_binary(!slot_lit, role_present_lit);
        }

        // At most max_count slots can have this role
        // Standard roles: max_count = 1 (prevents duplicates like "Mayor, Mayor, Imp")
        // Experimental roles: max_count > 1 (e.g., Village Idiot can appear up to 3 times)
        let max_count = role.max_count() as usize;
        encode_at_most_n(&mut vars.instance, &slots_with_this_role, max_count);
    }

    let mut placeholders = Vec::new();

    // 5. Assert known roles in their slots, leave placeholders free
    for (slot_idx, spec) in specs.iter().enumerate() {
        match spec {
            RoleSpec::Known(role) => {
                let slot_lit = slot_role_vars[slot_idx][role];
                vars.instance.add_unit(slot_lit);
            }
            RoleSpec::Placeholder {
                name,
                team_constraint,
            } => {
                if let Some(team) = team_constraint {
                    for role in available_roles {
                        if role.team() != *team {
                            vars.instance.add_unit(!slot_role_vars[slot_idx][role]);
                        }
                    }
                }
                placeholders.push((name.clone(), *team_constraint));
            }
        }
    }

    // 6. CHAIN ENCODING: Build modification chains for distribution
    let base = RoleDistribution::base_setup(player_count);

    // For each team, build chain: base → after_role_i → after_role_j → final
    encode_distribution_chain(&mut vars, Team::Townsfolk, base.townsfolk);
    encode_distribution_chain(&mut vars, Team::Outsider, base.outsider);
    encode_distribution_chain(&mut vars, Team::Minion, base.minion);
    encode_distribution_chain(&mut vars, Team::Demon, base.demon);

    // 7. Role type matching: count slot assignments
    encode_role_type_matching(&mut vars, Team::Townsfolk, &slot_role_vars);
    encode_role_type_matching(&mut vars, Team::Outsider, &slot_role_vars);
    encode_role_type_matching(&mut vars, Team::Minion, &slot_role_vars);
    encode_role_type_matching(&mut vars, Team::Demon, &slot_role_vars);

    // 8. Physical bag substitution (Drunk)
    encode_physical_bag_constraints(&mut vars);

    (vars, placeholders, slot_role_vars)
}

// Helper: Build chain of modifications for a single team type
fn encode_distribution_chain(vars: &mut BagVariables, team: Team, base_count: u8) {
    // Find all roles that modify this team type, in enum order
    let modifying_roles: Vec<(usize, Role, i8)> = Role::all()
        .iter()
        .enumerate()
        .filter_map(|(idx, role)| {
            role.setup_modifier().and_then(|modifier| match modifier {
                SetupModifier::AdjustCounts {
                    remove_townsfolk,
                    add_outsiders,
                } => {
                    let delta = match team {
                        Team::Townsfolk => -(remove_townsfolk as i8),
                        Team::Outsider => add_outsiders as i8,
                        _ => 0,
                    };
                    if delta != 0 {
                        Some((idx, *role, delta))
                    } else {
                        None
                    }
                }
            })
        })
        .collect();

    if modifying_roles.is_empty() {
        // No modifiers - final equals base
        let count_vars: Vec<rustsat::types::Lit> = vars.get_count_vars(team).to_vec();
        for (count, &final_var) in count_vars.iter().enumerate() {
            let base_var = vars.instance.new_lit(); // We need base_X variables

            if count == base_count as usize {
                // Base count is true
                vars.instance.add_unit(base_var);
                // final = base (biconditional)
                vars.instance.add_binary(!base_var, final_var);
                vars.instance.add_binary(!final_var, base_var);
            } else {
                // Base count is false
                vars.instance.add_unit(!base_var);
                // final = base (biconditional)
                vars.instance.add_binary(!base_var, final_var);
                vars.instance.add_binary(!final_var, base_var);
            }
        }
        return;
    }

    // Get the size of the count array
    let count_vars: Vec<rustsat::types::Lit> = vars.get_count_vars(team).to_vec();
    let max_count = count_vars.len() - 1;

    // Create chain variables
    let mut prev_prefix_vars: Vec<rustsat::types::Lit> = Vec::new();
    for count in 0..=max_count {
        let var = vars.instance.new_lit();
        prev_prefix_vars.push(var);
        // Initialize base: only base_count is true
        if count == base_count as usize {
            vars.instance.add_unit(var);
        } else {
            vars.instance.add_unit(!var);
        }
    }

    // Build chain
    for (_role_idx, role, delta) in &modifying_roles {
        let mut current_prefix_vars: Vec<rustsat::types::Lit> = Vec::new();
        for _ in 0..=max_count {
            current_prefix_vars.push(vars.instance.new_lit());
        }

        let role_lit = vars.role_present[role];

        // Encode modification logic
        for count in 0..=max_count {
            let prev_var = prev_prefix_vars[count];
            let current_var = current_prefix_vars[count];

            let modified_count = (count as i8) + delta;

            if modified_count >= 0 && modified_count <= max_count as i8 {
                let modified_var = current_prefix_vars[modified_count as usize];
                // Role present: prev_count => current_(count+delta)
                vars.instance.add_clause(
                    vec![!role_lit, !prev_var, modified_var]
                        .into_iter()
                        .collect(),
                );
            }

            // Role not present: prev_count => current_count
            vars.instance
                .add_clause(vec![role_lit, !prev_var, current_var].into_iter().collect());
        }

        prev_prefix_vars = current_prefix_vars;
    }

    // Link final chain link to final variables
    for count in 0..=max_count {
        let chain_var = prev_prefix_vars[count];
        let final_var = count_vars[count];
        // Biconditional
        vars.instance.add_binary(!chain_var, final_var);
        vars.instance.add_binary(!final_var, chain_var);
    }
}

fn encode_role_type_matching(
    vars: &mut BagVariables,
    team: Team,
    slot_role_vars: &[std::collections::HashMap<Role, rustsat::types::Lit>],
) {
    // Collect all roles of this type that are actually in the slot maps
    // (this respects script filtering - only includes available roles)
    let roles_of_type: Vec<Role> = if let Some(first_slot) = slot_role_vars.first() {
        first_slot
            .keys()
            .filter(|r| r.team() == team)
            .copied()
            .collect()
    } else {
        Vec::new()
    };

    // CRITICAL FIX: Count slot assignments instead of role presence
    // This naturally prevents duplicates: each slot has exactly one role,
    // so counting "slots with Townsfolk roles" ensures distinct assignments
    let slot_assignments: Vec<rustsat::types::Lit> = slot_role_vars
        .iter()
        .flat_map(|slot_map| roles_of_type.iter().filter_map(move |r| slot_map.get(r).copied()))
        .collect();

    // Copy count_vars to avoid borrow conflict
    let count_vars: Vec<rustsat::types::Lit> = vars.get_count_vars(team).to_vec();

    // For each possible count k: if final_count[k], then exactly k slots have roles of this type
    for (k, &count_lit) in count_vars.iter().enumerate() {
        encode_conditional_exactly_n(&mut vars.instance, count_lit, &slot_assignments, k);
    }
}

fn encode_physical_bag_constraints(vars: &mut BagVariables) {
    let drunk_var = vars.role_present[&Role::Drunk];

    // For each type, encode the physical bag relationship
    // Drunk causes: physical_townsfolk = final_townsfolk + 1, physical_outsider = final_outsider - 1

    encode_physical_bag_for_type(vars, Team::Townsfolk, drunk_var, 1); // +1 if drunk
    encode_physical_bag_for_type(vars, Team::Outsider, drunk_var, -1); // -1 if drunk
    encode_physical_bag_for_type(vars, Team::Minion, drunk_var, 0); // no change
    encode_physical_bag_for_type(vars, Team::Demon, drunk_var, 0); // no change
}

fn encode_physical_bag_for_type(
    vars: &mut BagVariables,
    team: Team,
    drunk_var: rustsat::types::Lit,
    drunk_delta: i8,
) {
    let final_vars: Vec<rustsat::types::Lit> = vars.get_count_vars(team).to_vec();
    let physical_vars: Vec<rustsat::types::Lit> = vars.get_physical_count_vars(team).to_vec();

    let max_count = final_vars.len();

    // For each possible count:
    // If drunk_present AND final_count[k], then physical_count[k + drunk_delta]
    // If NOT drunk_present AND final_count[k], then physical_count[k]

    for k in 0..max_count {
        let final_k = final_vars[k];

        // Case 1: Drunk present
        let physical_k_with_drunk = k as i8 + drunk_delta;
        if physical_k_with_drunk >= 0 && (physical_k_with_drunk as usize) < max_count {
            let physical_modified = physical_vars[physical_k_with_drunk as usize];
            // drunk AND final[k] => physical[k + delta]
            vars.instance.add_clause(
                vec![!drunk_var, !final_k, physical_modified]
                    .into_iter()
                    .collect(),
            );
        } else if drunk_delta != 0 {
            // Impossible: drunk AND final[k] would put us out of bounds
            // So drunk AND final[k] must be false
            vars.instance.add_binary(!drunk_var, !final_k);
        }

        // Case 2: Drunk not present
        let physical_no_drunk = physical_vars[k];
        // NOT drunk AND final[k] => physical[k]
        vars.instance.add_clause(
            vec![drunk_var, !final_k, physical_no_drunk]
                .into_iter()
                .collect(),
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Test helpers: convenience wrappers for encoding without script filtering
    fn encode_bag_spec_legality(
        player_count: u8,
        specs: &[RoleSpec],
    ) -> EncodingResult {
        encode_bag_spec_legality_with_script(player_count, specs, None)
    }

    fn encode_bag_spec_legality_chain(
        player_count: u8,
        specs: &[RoleSpec],
    ) -> EncodingResult {
        encode_bag_spec_legality_chain_with_script(player_count, specs, None)
    }

    #[test]
    fn test_valid_7_player_base_setup() {
        // 7 players base setup: 5T/0O/1M/1D
        let player_count = 7;
        let selected_roles = vec![
            Role::Chef,
            Role::Empath,
            Role::FortuneTeller,
            Role::Monk,
            Role::Ravenkeeper, // 5 townsfolk
            Role::Poisoner,    // 1 minion
            Role::Imp,         // 1 demon
        ];

        let vars = encode_bag_legality(player_count, &selected_roles);

        let mut solver = rustsat_minisat::core::Minisat::default();
        solver.add_cnf(vars.instance.into_cnf().0).unwrap();
        let result = solver.solve().unwrap();

        assert_eq!(
            result,
            SolverResult::Sat,
            "Valid 7-player base setup should be SAT"
        );
    }

    #[test]
    fn test_invalid_7_player_wrong_counts() {
        // 7 players base setup requires 5T/0O/1M/1D
        // But we provide 4T/1O/1M/1D - should be UNSAT
        let player_count = 7;
        let selected_roles = vec![
            Role::Chef,
            Role::Empath,
            Role::FortuneTeller,
            Role::Monk,     // 4 townsfolk
            Role::Butler,   // 1 outsider (but base says 0!)
            Role::Poisoner, // 1 minion
            Role::Imp,      // 1 demon
        ];

        let vars = encode_bag_legality(player_count, &selected_roles);

        let mut solver = rustsat_minisat::core::Minisat::default();
        solver.add_cnf(vars.instance.into_cnf().0).unwrap();
        let result = solver.solve().unwrap();

        assert_eq!(
            result,
            SolverResult::Unsat,
            "Invalid distribution should be UNSAT"
        );
    }

    #[test]
    fn test_drunk_physical_bag_substitution() {
        // 6 players with Drunk: 3T/1O/1M/1D in-play
        // Physical bag should be 4T/0O/1M/1D (Drunk gets townsfolk token)
        let player_count = 6;
        let selected_roles = vec![
            Role::Chef,
            Role::Empath,
            Role::FortuneTeller, // 3 townsfolk
            Role::Drunk,         // 1 outsider (in-play) but draws townsfolk token
            Role::Poisoner,      // 1 minion
            Role::Imp,           // 1 demon
        ];

        let vars = encode_bag_legality(player_count, &selected_roles);

        let mut solver = rustsat_minisat::core::Minisat::default();
        solver.add_cnf(vars.instance.into_cnf().0).unwrap();
        let result = solver.solve().unwrap();

        assert_eq!(result, SolverResult::Sat, "Valid Drunk setup should be SAT");
    }

    #[test]
    fn test_baron_count_modifier() {
        // 7 players with Baron: base is 5T/0O/1M/1D
        // Baron modifies to: 3T/2O/1M/1D
        let player_count = 7;
        let selected_roles = vec![
            Role::Chef,
            Role::Empath,
            Role::FortuneTeller, // 3 townsfolk
            Role::Butler,
            Role::Recluse, // 2 outsiders
            Role::Baron,   // 1 minion (causes -2T, +2O)
            Role::Imp,     // 1 demon
        ];

        let vars = encode_bag_legality(player_count, &selected_roles);

        let mut solver = rustsat_minisat::core::Minisat::default();
        solver.add_cnf(vars.instance.into_cnf().0).unwrap();
        let result = solver.solve().unwrap();

        assert_eq!(result, SolverResult::Sat, "Valid Baron setup should be SAT");
    }

    #[test]
    fn test_parse_bag_basic() {
        let bag_str = "{chef empath fortune_teller monk ravenkeeper poisoner imp}";
        let roles = parse_bag(bag_str).unwrap();

        assert_eq!(roles.len(), 7);
        assert!(roles.contains(&Role::Chef));
        assert!(roles.contains(&Role::Empath));
        assert!(roles.contains(&Role::FortuneTeller));
        assert!(roles.contains(&Role::Imp));
    }

    #[test]
    fn test_parse_bag_empty() {
        let bag_str = "{}";
        let roles = parse_bag(bag_str).unwrap();
        assert_eq!(roles.len(), 0);
    }

    #[test]
    fn test_parse_bag_invalid_role() {
        let bag_str = "{chef invalid_role imp}";
        let result = parse_bag(bag_str);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Unknown role"));
    }

    #[test]
    fn test_format_bag_round_trip() {
        let roles = vec![Role::Chef, Role::Empath, Role::Imp];
        let formatted = format_bag(&roles);
        let parsed = parse_bag(&formatted).unwrap();

        // Should have same roles (order might differ since it's a bag)
        assert_eq!(parsed.len(), roles.len());
        for role in &roles {
            assert!(parsed.contains(role));
        }
    }

    #[test]
    fn test_parse_bag_with_commas() {
        // Test Clojure-style comma as whitespace
        let bag_str = "{soldier, mayor imp, poisoner}";
        let roles = parse_bag(bag_str).unwrap();

        assert_eq!(roles.len(), 4);
        assert!(roles.contains(&Role::Soldier));
        assert!(roles.contains(&Role::Mayor));
        assert!(roles.contains(&Role::Imp));
        assert!(roles.contains(&Role::Poisoner));

        // Test that purely comma-separated also works
        let bag_str2 = "{chef,empath,imp}";
        let roles2 = parse_bag(bag_str2).unwrap();
        assert_eq!(roles2.len(), 3);
        assert!(roles2.contains(&Role::Chef));
        assert!(roles2.contains(&Role::Empath));
        assert!(roles2.contains(&Role::Imp));
    }

    #[test]
    fn test_placeholder_no_duplicates() {
        // Test that placeholders get assigned distinct roles
        let player_count = 3;
        let specs = vec![
            RoleSpec::Placeholder {
                name: "a".to_string(),
                team_constraint: None,
            },
            RoleSpec::Placeholder {
                name: "b".to_string(),
                team_constraint: None,
            },
            RoleSpec::Known(Role::Imp),
        ];

        let (vars, _placeholders, slot_vars) = encode_bag_spec_legality(player_count, &specs);

        let mut solver = rustsat_minisat::core::Minisat::default();
        solver.add_cnf(vars.instance.into_cnf().0).unwrap();
        let result = solver.solve().unwrap();

        assert_eq!(result, SolverResult::Sat, "3-player with 2 placeholders should be SAT");

        // Extract roles from slots
        let mut roles_in_slots = Vec::new();
        for slot_map in slot_vars.iter().take(specs.len()) {
            for role in Role::all() {
                if let Ok(rustsat::types::TernaryVal::True) = solver.lit_val(slot_map[role]) {
                    roles_in_slots.push(*role);
                    break;
                }
            }
        }

        // Check no duplicates exceed max_count
        let mut role_counts = std::collections::HashMap::new();
        for role in &roles_in_slots {
            *role_counts.entry(role).or_insert(0) += 1;
        }

        for (role, count) in role_counts {
            assert!(
                count <= role.max_count() as usize,
                "Role {:?} appears {} times but max_count is {}",
                role,
                count,
                role.max_count()
            );
        }
    }

    #[test]
    fn test_village_idiot_allows_duplicates() {
        // Village Idiot should be allowed to appear multiple times
        let player_count = 8;
        let specs = vec![
            RoleSpec::Known(Role::VillageIdiot),
            RoleSpec::Known(Role::VillageIdiot),
            RoleSpec::Placeholder { name: "a".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "b".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "c".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "d".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "e".to_string(), team_constraint: None },
            RoleSpec::Known(Role::Imp),
        ];

        let (vars, _placeholders, _slot_vars) = encode_bag_spec_legality(player_count, &specs);

        let mut solver = rustsat_minisat::core::Minisat::default();
        solver.add_cnf(vars.instance.into_cnf().0).unwrap();
        let result = solver.solve().unwrap();

        assert_eq!(result, SolverResult::Sat, "Village Idiot should be allowed multiple times");
    }

    #[test]
    fn test_team_constrained_placeholder() {
        // Test that team constraints work
        let player_count = 4;
        let specs = vec![
            RoleSpec::Placeholder {
                name: "townsfolk".to_string(),
                team_constraint: Some(Team::Townsfolk),
            },
            RoleSpec::Placeholder {
                name: "another_townsfolk".to_string(),
                team_constraint: Some(Team::Townsfolk),
            },
            RoleSpec::Placeholder {
                name: "minion".to_string(),
                team_constraint: Some(Team::Minion),
            },
            RoleSpec::Known(Role::Imp),
        ];

        let (vars, _placeholders, slot_vars) = encode_bag_spec_legality(player_count, &specs);

        let mut solver = rustsat_minisat::core::Minisat::default();
        solver.add_cnf(vars.instance.into_cnf().0).unwrap();
        let result = solver.solve().unwrap();

        assert_eq!(result, SolverResult::Sat, "Team-constrained placeholders should be SAT");

        // Verify team constraints were respected
        for (slot_idx, (spec, slot_map)) in specs.iter().zip(slot_vars.iter()).enumerate() {
            if let RoleSpec::Placeholder { team_constraint: Some(expected_team), .. } = spec {
                for role in Role::all() {
                    if let Ok(rustsat::types::TernaryVal::True) = solver.lit_val(slot_map[role]) {
                        assert_eq!(
                            role.team(),
                            *expected_team,
                            "Placeholder slot {} should have team {:?}, but got {:?}",
                            slot_idx,
                            expected_team,
                            role.team()
                        );
                        break;
                    }
                }
            }
        }
    }

    #[test]
    fn test_one_outsider_implies_baron() {
        // Key test: In a 7-player game (base: 5T/0O/1M/1D), if we have 1 Outsider,
        // Baron MUST be present (only modifier that adds Outsiders).
        // And Baron adds exactly 2 Outsiders, so we must have 2 total.
        let player_count = 7;
        let specs = vec![
            RoleSpec::Known(Role::Butler), // 1 Outsider explicitly present
            RoleSpec::Placeholder { name: "a".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "b".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "c".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "d".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "e".to_string(), team_constraint: None },
            RoleSpec::Known(Role::Imp),
        ];

        let (vars, _placeholders, slot_vars) = encode_bag_spec_legality(player_count, &specs);

        let mut solver = rustsat_minisat::core::Minisat::default();
        solver.add_cnf(vars.instance.into_cnf().0).unwrap();
        let result = solver.solve().unwrap();

        assert_eq!(result, SolverResult::Sat, "7-player with 1 Outsider should be SAT (Baron inferred)");

        // Extract the solution
        let mut roles_in_slots = Vec::new();
        for slot_map in slot_vars.iter().take(specs.len()) {
            for role in Role::all() {
                if let Ok(rustsat::types::TernaryVal::True) = solver.lit_val(slot_map[role]) {
                    roles_in_slots.push(*role);
                    break;
                }
            }
        }

        // Count by team
        let mut outsider_count = 0;
        let mut baron_present = false;
        for role in &roles_in_slots {
            if role.team() == Team::Outsider {
                outsider_count += 1;
            }
            if *role == Role::Baron {
                baron_present = true;
            }
        }

        // Key assertions:
        // 1. Baron must be present (only way to have Outsiders in 7-player)
        assert!(baron_present, "Baron must be present when we have an Outsider in 7-player game");

        // 2. We must have exactly 2 Outsiders (Baron's modifier: -2T/+2O)
        assert_eq!(outsider_count, 2, "Baron adds exactly 2 Outsiders, so we need 2 total");
    }

    #[test]
    fn test_trouble_brewing_script() {
        let script = Script::trouble_brewing();

        // Village Idiot is not in Trouble Brewing
        assert!(!script.roles.contains(&Role::VillageIdiot));

        // Imp is in Trouble Brewing
        assert!(script.roles.contains(&Role::Imp));

        // Mayor is in Trouble Brewing
        assert!(script.roles.contains(&Role::Mayor));
    }

    #[test]
    fn test_script_filtering_in_solver() {
        // Test that script filtering prevents non-script roles from being assigned to placeholders
        let script = Script::trouble_brewing();
        let player_count = 4;
        let specs = vec![
            RoleSpec::Placeholder {
                name: "a".to_string(),
                team_constraint: Some(Team::Townsfolk),
            },
            RoleSpec::Placeholder {
                name: "b".to_string(),
                team_constraint: Some(Team::Townsfolk),
            },
            RoleSpec::Placeholder {
                name: "c".to_string(),
                team_constraint: Some(Team::Minion),
            },
            RoleSpec::Known(Role::Imp),
        ];

        let (vars, _placeholders, slot_vars) =
            encode_bag_spec_legality_with_script(player_count, &specs, Some(&script));

        let mut solver = rustsat_minisat::core::Minisat::default();
        solver.add_cnf(vars.instance.into_cnf().0).unwrap();
        let result = solver.solve().unwrap();

        assert_eq!(
            result,
            SolverResult::Sat,
            "4-player TB script should be SAT"
        );

        // Extract roles from slots and verify none are experimental
        for slot_map in slot_vars.iter().take(specs.len()) {
            for role in Role::all() {
                if let Some(&slot_lit) = slot_map.get(role) {
                    if let Ok(rustsat::types::TernaryVal::True) = solver.lit_val(slot_lit) {
                        // This role was assigned to this slot
                        // Verify it's in the Trouble Brewing script
                        assert!(
                            script.roles.contains(role),
                            "Role {:?} was assigned but is not in Trouble Brewing script",
                            role
                        );

                        // Specifically verify Village Idiot is never assigned
                        assert_ne!(
                            *role,
                            Role::VillageIdiot,
                            "Village Idiot should not be assigned with TB script"
                        );
                        break;
                    }
                }
            }
        }
    }

    // Chain encoding tests - verify chain encoding strategy works correctly

    #[test]
    fn test_placeholder_no_duplicates_chain() {
        // Same as test_placeholder_no_duplicates but using chain encoding
        let player_count = 7;
        let specs = vec![
            RoleSpec::Known(Role::Imp),
            RoleSpec::Placeholder { name: "a".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "b".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "c".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "d".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "e".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "f".to_string(), team_constraint: None },
        ];

        let (vars, _placeholders, slot_vars) = encode_bag_spec_legality_chain(player_count, &specs);

        let mut solver = rustsat_minisat::core::Minisat::default();
        solver.add_cnf(vars.instance.into_cnf().0).unwrap();
        let result = solver.solve().unwrap();

        assert_eq!(result, SolverResult::Sat, "Placeholders should be SAT");

        // Extract solution and verify no duplicates
        let mut roles_in_slots = Vec::new();
        for slot_map in slot_vars.iter().take(specs.len()) {
            for role in Role::all() {
                if let Ok(rustsat::types::TernaryVal::True) = solver.lit_val(slot_map[role]) {
                    roles_in_slots.push(*role);
                    break;
                }
            }
        }

        // Check for duplicates
        let mut role_counts = std::collections::HashMap::new();
        for role in &roles_in_slots {
            *role_counts.entry(role).or_insert(0) += 1;
        }

        for (role, count) in role_counts {
            let max_allowed = role.max_count() as usize;
            assert!(
                count <= max_allowed,
                "Role {:?} appears {} times but max_count is {}",
                role,
                count,
                max_allowed
            );
        }
    }

    #[test]
    fn test_team_constrained_placeholder_chain() {
        // Same as test_team_constrained_placeholder but using chain encoding
        let player_count = 7;
        let specs = vec![
            RoleSpec::Known(Role::Imp),
            RoleSpec::Placeholder {
                name: "outsider".to_string(),
                team_constraint: Some(Team::Outsider),
            },
            RoleSpec::Placeholder {
                name: "minion".to_string(),
                team_constraint: Some(Team::Minion),
            },
            RoleSpec::Placeholder { name: "a".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "b".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "c".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "d".to_string(), team_constraint: None },
        ];

        let (vars, _placeholders, slot_vars) = encode_bag_spec_legality_chain(player_count, &specs);

        let mut solver = rustsat_minisat::core::Minisat::default();
        solver.add_cnf(vars.instance.into_cnf().0).unwrap();
        let result = solver.solve().unwrap();

        assert_eq!(result, SolverResult::Sat, "Team-constrained placeholders should be SAT");

        // Verify team constraints were respected
        for (slot_idx, (spec, slot_map)) in specs.iter().zip(slot_vars.iter()).enumerate() {
            if let RoleSpec::Placeholder { team_constraint: Some(expected_team), .. } = spec {
                for role in Role::all() {
                    if let Ok(rustsat::types::TernaryVal::True) = solver.lit_val(slot_map[role]) {
                        assert_eq!(
                            role.team(),
                            *expected_team,
                            "Placeholder slot {} should have team {:?}, but got {:?}",
                            slot_idx,
                            expected_team,
                            role.team()
                        );
                        break;
                    }
                }
            }
        }
    }

    #[test]
    fn test_script_filtering_in_solver_chain() {
        // Same as test_script_filtering_in_solver but using chain encoding
        let script = Script::trouble_brewing();
        let player_count = 4;
        let specs = vec![
            RoleSpec::Placeholder {
                name: "a".to_string(),
                team_constraint: Some(Team::Townsfolk),
            },
            RoleSpec::Placeholder {
                name: "b".to_string(),
                team_constraint: Some(Team::Townsfolk),
            },
            RoleSpec::Placeholder {
                name: "c".to_string(),
                team_constraint: Some(Team::Minion),
            },
            RoleSpec::Known(Role::Imp),
        ];

        let (vars, _placeholders, slot_vars) =
            encode_bag_spec_legality_chain_with_script(player_count, &specs, Some(&script));

        let mut solver = rustsat_minisat::core::Minisat::default();
        solver.add_cnf(vars.instance.into_cnf().0).unwrap();
        let result = solver.solve().unwrap();

        assert_eq!(
            result,
            SolverResult::Sat,
            "4-player TB script should be SAT"
        );

        // Extract roles from slots and verify none are experimental
        for slot_map in slot_vars.iter().take(specs.len()) {
            for role in Role::all() {
                if let Some(&slot_lit) = slot_map.get(role) {
                    if let Ok(rustsat::types::TernaryVal::True) = solver.lit_val(slot_lit) {
                        // This role was assigned to this slot
                        // Verify it's in the Trouble Brewing script
                        assert!(
                            script.roles.contains(role),
                            "Role {:?} was assigned but is not in Trouble Brewing script",
                            role
                        );

                        // Specifically verify Village Idiot is never assigned
                        assert_ne!(
                            *role,
                            Role::VillageIdiot,
                            "Village Idiot should not be assigned with TB script"
                        );
                        break;
                    }
                }
            }
        }
    }

    #[test]
    fn test_one_outsider_implies_baron_chain() {
        // Same as test_one_outsider_implies_baron but using chain encoding
        let player_count = 7;
        let specs = vec![
            RoleSpec::Known(Role::Butler), // 1 Outsider explicitly present
            RoleSpec::Placeholder { name: "a".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "b".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "c".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "d".to_string(), team_constraint: None },
            RoleSpec::Placeholder { name: "e".to_string(), team_constraint: None },
            RoleSpec::Known(Role::Imp),
        ];

        let (vars, _placeholders, slot_vars) = encode_bag_spec_legality_chain(player_count, &specs);

        let mut solver = rustsat_minisat::core::Minisat::default();
        solver.add_cnf(vars.instance.into_cnf().0).unwrap();
        let result = solver.solve().unwrap();

        assert_eq!(result, SolverResult::Sat, "7-player with 1 Outsider should be SAT (Baron inferred)");

        // Extract the solution
        let mut roles_in_slots = Vec::new();
        for slot_map in slot_vars.iter().take(specs.len()) {
            for role in Role::all() {
                if let Ok(rustsat::types::TernaryVal::True) = solver.lit_val(slot_map[role]) {
                    roles_in_slots.push(*role);
                    break;
                }
            }
        }

        // Count by team
        let mut outsider_count = 0;
        let mut baron_present = false;
        for role in &roles_in_slots {
            if role.team() == Team::Outsider {
                outsider_count += 1;
            }
            if *role == Role::Baron {
                baron_present = true;
            }
        }

        // Key assertions:
        // 1. Baron must be present (only way to have Outsiders in 7-player)
        assert!(baron_present, "Baron must be present when we have an Outsider in 7-player game");

        // 2. We must have exactly 2 Outsiders (Baron's modifier: -2T/+2O)
        assert_eq!(outsider_count, 2, "Baron adds exactly 2 Outsiders, so we need 2 total");
    }

    // ===== GRIMOIRE PARSER TESTS =====

    #[test]
    fn test_parse_grimoire_basic() {
        let grimoire_str = "[Alice:baron Bob:imp Charlie:butler]";
        let grimoire = parse_grimoire(grimoire_str).unwrap();

        assert_eq!(grimoire.players.len(), 3);

        assert_eq!(grimoire.players[0].name, "Alice");
        assert_eq!(grimoire.players[0].role, "baron");
        assert!(grimoire.players[0].alive);
        assert!(grimoire.players[0].has_ghost_vote);
        assert!(grimoire.players[0].reminder_tokens.is_empty());

        assert_eq!(grimoire.players[1].name, "Bob");
        assert_eq!(grimoire.players[1].role, "imp");

        assert_eq!(grimoire.players[2].name, "Charlie");
        assert_eq!(grimoire.players[2].role, "butler");
    }

    #[test]
    fn test_parse_grimoire_with_tokens() {
        let grimoire_str = "[Alice:baron(poi:poisoned,ww:townsfolk) Bob:imp]";
        let grimoire = parse_grimoire(grimoire_str).unwrap();

        assert_eq!(grimoire.players.len(), 2);
        assert_eq!(grimoire.players[0].name, "Alice");
        assert_eq!(grimoire.players[0].reminder_tokens.len(), 2);
        assert_eq!(grimoire.players[0].reminder_tokens[0], "poi:poisoned");
        assert_eq!(grimoire.players[0].reminder_tokens[1], "ww:townsfolk");
    }

    #[test]
    fn test_parse_grimoire_dead_with_ghost_vote() {
        let grimoire_str = "[Alice:baron *Bob:imp*]";
        let grimoire = parse_grimoire(grimoire_str).unwrap();

        assert_eq!(grimoire.players.len(), 2);
        assert!(grimoire.players[0].alive);
        assert!(!grimoire.players[1].alive);
        assert!(grimoire.players[1].has_ghost_vote);
        assert_eq!(grimoire.players[1].name, "Bob");
        assert_eq!(grimoire.players[1].role, "imp");
    }

    #[test]
    fn test_parse_grimoire_dead_without_ghost_vote() {
        let grimoire_str = "[Alice:baron *~~Bob~~:imp*]";
        let grimoire = parse_grimoire(grimoire_str).unwrap();

        assert_eq!(grimoire.players.len(), 2);
        assert!(!grimoire.players[1].alive);
        assert!(!grimoire.players[1].has_ghost_vote);
        assert_eq!(grimoire.players[1].name, "Bob");
        assert_eq!(grimoire.players[1].role, "imp");
    }

    #[test]
    fn test_parse_grimoire_mixed_states() {
        let grimoire_str = "[Alice:baron(poi:poisoned) *Bob:imp* *~~Charlie~~:butler* Dave:washerwoman]";
        let grimoire = parse_grimoire(grimoire_str).unwrap();

        assert_eq!(grimoire.players.len(), 4);

        // Alice: alive with tokens
        assert!(grimoire.players[0].alive);
        assert_eq!(grimoire.players[0].reminder_tokens.len(), 1);

        // Bob: dead with ghost vote
        assert!(!grimoire.players[1].alive);
        assert!(grimoire.players[1].has_ghost_vote);

        // Charlie: dead without ghost vote
        assert!(!grimoire.players[2].alive);
        assert!(!grimoire.players[2].has_ghost_vote);

        // Dave: alive
        assert!(grimoire.players[3].alive);
        assert!(grimoire.players[3].has_ghost_vote);
    }

    #[test]
    fn test_parse_grimoire_empty() {
        let grimoire_str = "[]";
        let grimoire = parse_grimoire(grimoire_str).unwrap();
        assert_eq!(grimoire.players.len(), 0);
    }

    #[test]
    fn test_parse_grimoire_with_commas() {
        let grimoire_str = "[Alice:baron, Bob:imp, Charlie:butler]";
        let grimoire = parse_grimoire(grimoire_str).unwrap();
        assert_eq!(grimoire.players.len(), 3);
    }

    #[test]
    fn test_parse_grimoire_invalid_format() {
        let result = parse_grimoire("Alice:baron Bob:imp");
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("square brackets"));
    }

    // ===== GRIMOIRE LAYOUT TESTS =====

    #[test]
    fn test_generate_turn_configurations() {
        let configs = generate_all_turn_configurations(3);

        // Should generate all valid distributions across 6 segments
        assert!(!configs.is_empty());

        // Check that all configs sum to player count
        for config in &configs {
            let total = config.top_count
                + config.right_upper_count
                + config.right_lower_count
                + config.bottom_count
                + config.left_lower_count
                + config.left_upper_count;
            assert_eq!(total, 3);
            // Top count must be at least 1
            assert!(config.top_count >= 1);
        }
    }

    #[test]
    fn test_assign_players_to_sides() {
        let players = vec![
            PlayerState {
                name: "Alice".to_string(),
                role: "baron".to_string(),
                alive: true,
                has_ghost_vote: true,
                reminder_tokens: vec![],
            },
            PlayerState {
                name: "Bob".to_string(),
                role: "imp".to_string(),
                alive: true,
                has_ghost_vote: true,
                reminder_tokens: vec![],
            },
            PlayerState {
                name: "Charlie".to_string(),
                role: "butler".to_string(),
                alive: true,
                has_ghost_vote: true,
                reminder_tokens: vec![],
            },
        ];

        let layout = TurnBasedLayout {
            top_count: 2,
            right_upper_count: 0,
            right_lower_count: 0,
            bottom_count: 1,
            left_lower_count: 0,
            left_upper_count: 0,
        };

        let positions = assign_players_to_sides(&players, &layout);

        assert_eq!(positions.len(), 3);

        // First two players on top
        assert!(matches!(positions[0].side, Side::Top));
        assert_eq!(positions[0].side_index, 0);
        assert_eq!(positions[0].player.name, "Alice");

        assert!(matches!(positions[1].side, Side::Top));
        assert_eq!(positions[1].side_index, 1);
        assert_eq!(positions[1].player.name, "Bob");

        // Third player on bottom
        assert!(matches!(positions[2].side, Side::Bottom));
        assert_eq!(positions[2].side_index, 0);
        assert_eq!(positions[2].player.name, "Charlie");
    }

    #[test]
    fn test_format_player_display_text() {
        let alive_player = PlayerState {
            name: "Alice".to_string(),
            role: "baron".to_string(),
            alive: true,
            has_ghost_vote: true,
            reminder_tokens: vec![],
        };

        let dead_with_vote = PlayerState {
            name: "Bob".to_string(),
            role: "imp".to_string(),
            alive: false,
            has_ghost_vote: true,
            reminder_tokens: vec![],
        };

        let dead_without_vote = PlayerState {
            name: "Charlie".to_string(),
            role: "butler".to_string(),
            alive: false,
            has_ghost_vote: false,
            reminder_tokens: vec![],
        };

        assert_eq!(format_player_display_text(&alive_player, false), "Alice");
        assert_eq!(format_player_display_text(&dead_with_vote, false), "*Bob*");
        assert_eq!(format_player_display_text(&dead_without_vote, false), "*~~Charlie~~*");

        // Worst case formatting
        assert_eq!(format_player_display_text(&alive_player, true), "*~~Alice~~*");
    }
}

// RoleSpec: Either a known role or a placeholder to be solved for
#[derive(Debug, Clone, PartialEq, Eq)]
enum RoleSpec {
    Known(Role),
    Placeholder {
        name: String,
        team_constraint: Option<Team>,
    },
}

// Parse a bag specification that may contain placeholders
fn parse_bag_spec_filtered(input: &str, script: Option<&Script>) -> Result<Vec<RoleSpec>, String> {
    let trimmed = input.trim();

    // Check for curly braces
    if !trimmed.starts_with('{') || !trimmed.ends_with('}') {
        return Err(format!("Bag must be enclosed in curly braces: {}", input));
    }

    // Extract content between braces
    let content = &trimmed[1..trimmed.len() - 1].trim();

    if content.is_empty() {
        return Ok(Vec::new());
    }

    // Split by whitespace and commas (Clojure-style)
    let tokens: Vec<&str> = content.split(|c: char| c.is_whitespace() || c == ',')
        .filter(|s| !s.is_empty())
        .collect();

    let mut specs = Vec::new();
    let mut role_counts: std::collections::HashMap<Role, usize> = std::collections::HashMap::new();

    for token in tokens {
        // Check if it's a placeholder: ?identifier? or ?team:identifier?
        if token.starts_with('?') && token.ends_with('?') {
            let inner = &token[1..token.len() - 1];

            if inner.is_empty() {
                return Err("Empty placeholder '??' is not supported yet".to_string());
            }

            // Check for team constraint: ?team:name?
            if let Some(colon_pos) = inner.find(':') {
                let team_str = &inner[..colon_pos];
                let name = &inner[colon_pos + 1..];

                if name.is_empty() {
                    return Err(format!(
                        "Placeholder '{}' has empty name after colon",
                        token
                    ));
                }

                let team = Team::from_str_or_shorthand(team_str).ok_or_else(|| {
                    format!("Unknown team '{}' in placeholder '{}'", team_str, token)
                })?;

                specs.push(RoleSpec::Placeholder {
                    name: name.to_string(),
                    team_constraint: Some(team),
                });
            } else {
                // Check if the placeholder name itself is a team name
                // e.g., ?outsider? should be constrained to Outsider team
                if let Some(team) = Team::from_str_or_shorthand(inner) {
                    specs.push(RoleSpec::Placeholder {
                        name: inner.to_string(),
                        team_constraint: Some(team),
                    });
                } else {
                    // Unconstrained placeholder
                    specs.push(RoleSpec::Placeholder {
                        name: inner.to_string(),
                        team_constraint: None,
                    });
                }
            }
        } else {
            // Try to parse as a known role
            let role = match_role_name_filtered(token, script)?;

            // Check for duplicates - only allowed for roles with max_count > 1
            let current_count = role_counts.get(&role).copied().unwrap_or(0);
            if current_count >= role.max_count() as usize {
                return Err(format!(
                    "Too many instances of '{}' in bag. \
                     Maximum allowed: {}, found: {}",
                    role.name(),
                    role.max_count(),
                    current_count + 1
                ));
            }
            *role_counts.entry(role).or_insert(0) += 1;

            specs.push(RoleSpec::Known(role));
        }
    }

    Ok(specs)
}

// Bag parsing: parse textual representation "{role1 role2 ...}"
#[allow(dead_code)]
fn parse_bag(input: &str) -> Result<Vec<Role>, String> {
    let trimmed = input.trim();

    // Check for curly braces
    if !trimmed.starts_with('{') || !trimmed.ends_with('}') {
        return Err(format!("Bag must be enclosed in curly braces: {}", input));
    }

    // Extract content between braces
    let content = &trimmed[1..trimmed.len() - 1].trim();

    if content.is_empty() {
        return Ok(Vec::new());
    }

    // Split by whitespace and commas (Clojure-style)
    let role_names: Vec<&str> = content.split(|c: char| c.is_whitespace() || c == ',')
        .filter(|s| !s.is_empty())
        .collect();
    let mut roles = Vec::new();

    for role_name in role_names {
        // Try to match role name
        let role = match_role_name(role_name)?;
        roles.push(role);
    }

    Ok(roles)
}

fn match_role_name(name: &str) -> Result<Role, String> {
    match_role_name_filtered(name, None)
}

fn match_role_name_filtered(name: &str, script: Option<&Script>) -> Result<Role, String> {
    let normalized_input = name.to_lowercase();

    let roles_to_search = if let Some(script) = script {
        &script.roles
    } else {
        Role::all()
    };

    // Try exact match first (case-insensitive, with underscores)
    for role in roles_to_search {
        let normalized_role = role.name().to_lowercase().replace(' ', "_");
        if normalized_role == normalized_input {
            return Ok(*role);
        }
    }

    // No exact match - find close suggestions using Jaro-Winkler similarity
    let mut suggestions: Vec<_> = roles_to_search
        .iter()
        .map(|role| {
            let normalized_role = role.name().to_lowercase().replace(' ', "_");
            let similarity = strsim::jaro_winkler(&normalized_input, &normalized_role);
            (role, similarity)
        })
        .filter(|(_, sim)| *sim >= 0.7) // At least 70% similar
        .collect();

    suggestions.sort_by(|(_, a), (_, b)| b.partial_cmp(a).unwrap()); // Sort by similarity descending

    if let Some((closest_role, similarity)) = suggestions.first() {
        if *similarity >= 0.85 {
            // Very close match - suggest just this one
            Err(format!(
                "Unknown role name: '{}'\n  Did you mean: {}?",
                name,
                closest_role.name().to_lowercase().replace(' ', "_")
            ))
        } else {
            // Multiple possible matches
            let suggestion_names: Vec<_> = suggestions
                .iter()
                .take(3)
                .map(|(r, _)| r.name().to_lowercase().replace(' ', "_"))
                .collect();
            Err(format!(
                "Unknown role name: '{}'\n  Did you mean one of: {}?",
                name,
                suggestion_names.join(", ")
            ))
        }
    } else {
        Err(format!("Unknown role name: '{}'", name))
    }
}

// ===== GRIMOIRE RENDERING =====

/// Represents a player's state in the grimoire
#[derive(Debug, Clone, PartialEq)]
struct PlayerState {
    name: String,
    role: String,
    alive: bool,
    has_ghost_vote: bool,
    reminder_tokens: Vec<String>,
}

/// Represents the complete grimoire state
#[derive(Debug, Clone, PartialEq)]
struct GrimoireState {
    players: Vec<PlayerState>,
}

/// Parse grimoire from single-line format: [Alice:baron Bob:imp *Charlie:butler*]
fn parse_grimoire(input: &str) -> Result<GrimoireState, String> {
    let trimmed = input.trim();

    // Check for square brackets
    if !trimmed.starts_with('[') || !trimmed.ends_with(']') {
        return Err(format!("Grimoire must be enclosed in square brackets: {}", input));
    }

    // Extract content between brackets
    let content = &trimmed[1..trimmed.len() - 1].trim();

    if content.is_empty() {
        return Ok(GrimoireState { players: Vec::new() });
    }

    // Split by whitespace and commas, but NOT inside parentheses
    let tokens = split_player_entries(content);

    let mut players = Vec::new();

    for token in tokens {
        players.push(parse_player_entry(token)?);
    }

    Ok(GrimoireState { players })
}

/// Split player entries, respecting parentheses (don't split on commas inside parens)
fn split_player_entries(content: &str) -> Vec<&str> {
    let mut entries = Vec::new();
    let mut current_start = 0;
    let mut paren_depth = 0;
    let chars: Vec<char> = content.chars().collect();

    for (i, &ch) in chars.iter().enumerate() {
        match ch {
            '(' => paren_depth += 1,
            ')' => paren_depth -= 1,
            _ if paren_depth == 0 && (ch.is_whitespace() || ch == ',') => {
                // Split here
                let entry = &content[current_start..i].trim();
                if !entry.is_empty() {
                    entries.push(*entry);
                }
                current_start = i + 1;
            }
            _ => {}
        }
    }

    // Add the last entry
    let entry = &content[current_start..].trim();
    if !entry.is_empty() {
        entries.push(*entry);
    }

    entries
}

/// Parse a single player entry: Alice:baron or *Bob:imp* or *~~Charlie~~:butler(poi:poisoned)*
fn parse_player_entry(entry: &str) -> Result<PlayerState, String> {
    let entry = entry.trim();

    // Check if dead (surrounded by *)
    if entry.starts_with('*') && entry.ends_with('*') {
        // Dead player
        let inner = &entry[1..entry.len() - 1];

        // Check if ghost vote used (~~name~~)
        let (name_part, has_ghost_vote) = if inner.starts_with("~~") && inner.contains("~~:") {
            // Extract name between ~~
            let end_tilde_idx = inner[2..].find("~~").ok_or_else(|| {
                format!("Invalid dead player format (missing closing ~~): {}", entry)
            })? + 2;
            let name = &inner[2..end_tilde_idx];
            let rest = &inner[end_tilde_idx + 2 + 1..]; // Skip the closing ~~ and the :
            (format!("{}:{}", name, rest), false)
        } else {
            (inner.to_string(), true)
        };

        parse_player_parts(&name_part, false, has_ghost_vote)
    } else {
        // Living player
        parse_player_parts(entry, true, true)
    }
}

/// Parse player parts: name:role or name:role(tokens)
fn parse_player_parts(input: &str, alive: bool, has_ghost_vote: bool) -> Result<PlayerState, String> {
    // Find the role part (before tokens if any)
    let (name_role_part, tokens_part) = if let Some(paren_idx) = input.find('(') {
        if !input.ends_with(')') {
            return Err(format!("Invalid token format (missing closing paren): {}", input));
        }
        (&input[..paren_idx], Some(&input[paren_idx + 1..input.len() - 1]))
    } else {
        (input, None)
    };

    // Split name and role by colon
    let parts: Vec<&str> = name_role_part.split(':').collect();
    if parts.len() != 2 {
        return Err(format!(
            "Invalid player format (expected name:role): {}",
            name_role_part
        ));
    }

    let name = parts[0].trim().to_string();
    let role = parts[1].trim().to_string();

    if name.is_empty() {
        return Err(format!("Player name cannot be empty: {}", input));
    }
    if role.is_empty() {
        return Err(format!("Player role cannot be empty: {}", input));
    }

    // Parse tokens if present
    let reminder_tokens = if let Some(tokens_str) = tokens_part {
        tokens_str
            .split(',')
            .map(|t| t.trim().to_string())
            .filter(|t| !t.is_empty())
            .collect()
    } else {
        Vec::new()
    };

    Ok(PlayerState {
        name,
        role,
        alive,
        has_ghost_vote,
        reminder_tokens,
    })
}

// ===== GRIMOIRE RENDERING - LAYOUT SYSTEM =====

/// Turn-based layout: distribution of players across 6 segments (V-shaped vertical sides)
///
/// The layout follows clockwise order:
/// - Top: horizontal, left to right
/// - RightUpper: upper arm of right V (receding from right edge toward center)
/// - RightLower: lower arm of right V (receding from right edge toward center)
/// - Bottom: horizontal, right to left
/// - LeftLower: lower arm of left V (receding from left edge toward center)
/// - LeftUpper: upper arm of left V (receding from left edge toward center)
///
/// The "apex" of each V is the transition between upper/lower segments.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct TurnBasedLayout {
    top_count: usize,
    right_upper_count: usize,
    right_lower_count: usize,
    bottom_count: usize,
    left_lower_count: usize,
    left_upper_count: usize,
}

/// Player position segment
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Side {
    Top,
    RightUpper,
    RightLower,
    Bottom,
    LeftLower,
    LeftUpper,
}

/// A player assigned to a side with their position
#[derive(Debug, Clone)]
struct PlayerPosition<'a> {
    player: &'a PlayerState,
    side: Side,
    side_index: usize, // Position within that side (0-based)
}

/// Generate all possible turn configurations for a given player count
/// Returns all valid ways to distribute players across 6 segments
fn generate_all_turn_configurations(player_count: usize) -> Vec<TurnBasedLayout> {
    let mut configurations = Vec::new();

    // Try all possible ways to distribute players among 6 segments
    // Constraint: top_count >= 1 (at least one player on top for visual stability)
    for top_count in 1..=player_count {
        let remaining_after_top = player_count - top_count;

        for right_upper_count in 0..=remaining_after_top {
            let remaining_after_ru = remaining_after_top - right_upper_count;

            for right_lower_count in 0..=remaining_after_ru {
                let remaining_after_rl = remaining_after_ru - right_lower_count;

                for bottom_count in 0..=remaining_after_rl {
                    let remaining_after_bottom = remaining_after_rl - bottom_count;

                    for left_lower_count in 0..=remaining_after_bottom {
                        let left_upper_count = remaining_after_bottom - left_lower_count;

                        configurations.push(TurnBasedLayout {
                            top_count,
                            right_upper_count,
                            right_lower_count,
                            bottom_count,
                            left_lower_count,
                            left_upper_count,
                        });
                    }
                }
            }
        }
    }

    configurations
}

/// Assign players to segments based on turn configuration
/// Players are assigned in clockwise order through 6 segments
fn assign_players_to_sides<'a>(
    players: &'a [PlayerState],
    layout: &TurnBasedLayout,
) -> Vec<PlayerPosition<'a>> {
    let mut positions = Vec::new();
    let mut player_index = 0;

    // Top side (left to right)
    for i in 0..layout.top_count {
        positions.push(PlayerPosition {
            player: &players[player_index],
            side: Side::Top,
            side_index: i,
        });
        player_index += 1;
    }

    // Right upper (upper arm of V, going down toward apex)
    for i in 0..layout.right_upper_count {
        positions.push(PlayerPosition {
            player: &players[player_index],
            side: Side::RightUpper,
            side_index: i,
        });
        player_index += 1;
    }

    // Right lower (lower arm of V, going down from apex)
    for i in 0..layout.right_lower_count {
        positions.push(PlayerPosition {
            player: &players[player_index],
            side: Side::RightLower,
            side_index: i,
        });
        player_index += 1;
    }

    // Bottom side (right to left) - reverse for clockwise flow
    let bottom_start = player_index;
    player_index += layout.bottom_count;
    for i in 0..layout.bottom_count {
        positions.push(PlayerPosition {
            player: &players[bottom_start + layout.bottom_count - 1 - i],
            side: Side::Bottom,
            side_index: i,
        });
    }

    // Left lower (lower arm of V, going up toward apex)
    let left_lower_start = player_index;
    player_index += layout.left_lower_count;
    for i in 0..layout.left_lower_count {
        positions.push(PlayerPosition {
            player: &players[left_lower_start + layout.left_lower_count - 1 - i],
            side: Side::LeftLower,
            side_index: i,
        });
    }

    // Left upper (upper arm of V, going up from apex)
    let left_upper_start = player_index;
    player_index += layout.left_upper_count;
    for i in 0..layout.left_upper_count {
        positions.push(PlayerPosition {
            player: &players[left_upper_start + layout.left_upper_count - 1 - i],
            side: Side::LeftUpper,
            side_index: i,
        });
    }

    positions
}

// ===== GRIMOIRE RENDERING - GRID SYSTEM =====

/// A cell in the abstract grid
#[derive(Debug, Clone)]
struct GridCell {
    content: String,
    row: usize,
    col: usize,
}

/// Abstract grid representation
#[derive(Debug, Clone)]
struct AbstractGrid {
    cells: Vec<GridCell>,
    min_row: usize,
    max_row: usize,
    min_col: usize,
    max_col: usize,
}

impl AbstractGrid {
    fn new() -> Self {
        AbstractGrid {
            cells: Vec::new(),
            min_row: 0,
            max_row: 0,
            min_col: 0,
            max_col: 0,
        }
    }

    fn add_cell(&mut self, content: String, row: usize, col: usize) {
        if self.cells.is_empty() {
            self.min_row = row;
            self.max_row = row;
            self.min_col = col;
            self.max_col = col + content.len();
        } else {
            self.min_row = self.min_row.min(row);
            self.max_row = self.max_row.max(row);
            self.min_col = self.min_col.min(col);
            self.max_col = self.max_col.max(col + content.len());
        }

        self.cells.push(GridCell { content, row, col });
    }

    /// Get dimensions (width, height)
    fn dimensions(&self) -> (usize, usize) {
        if self.cells.is_empty() {
            (0, 0)
        } else {
            let width = self.max_col - self.min_col;
            let height = self.max_row - self.min_row + 1;
            (width, height)
        }
    }
}

/// Format player display text (handles alive/dead formatting)
fn format_player_display_text(player: &PlayerState, worst_case: bool) -> String {
    if worst_case {
        // Worst case formatting for layout stability: *~~name~~*
        format!("*~~{}~~*", player.name)
    } else if player.alive {
        player.name.clone()
    } else if player.has_ghost_vote {
        format!("*{}*", player.name)
    } else {
        format!("*~~{}~~*", player.name)
    }
}

// ===== GRIMOIRE RENDERING - POSITIONING =====

/// Calculate the indentation for a player based on their V-position
/// Returns the indentation amount (0 = sticks out most, higher = more indented)
fn calculate_v_indentation(segment_index: usize, segment_count: usize) -> usize {
    if segment_count == 0 {
        return 0;
    }
    if segment_count == 1 {
        return 0; // Single player, no indentation
    }

    // For V-shape: middle player (apex) has 0 indentation, others increase
    // segment_index goes from 0 to segment_count-1
    // Apex is at index segment_count-1 (last player in the segment)
    let distance_from_apex = (segment_count - 1).saturating_sub(segment_index);
    distance_from_apex * 3 // 3 spaces per level of indentation
}

/// Simple renderer that places players in a grid (simplified version)
fn render_grimoire_simple(grimoire: &GrimoireState, layout: &TurnBasedLayout) -> String {
    if grimoire.players.is_empty() {
        let mut grid = AbstractGrid::new();
        let title = "Grimoire (0 players)";
        return render_grid_to_ascii(&grid, title);
    }

    let positions = assign_players_to_sides(&grimoire.players, layout);
    let mut grid = AbstractGrid::new();

    // Constants for layout
    const PLAYER_SPACING: usize = 12; // Horizontal spacing between players
    const VERTICAL_SPACING: usize = 3; // Rows per player (name, role, blank)
    const SIDE_MARGIN: usize = 2; // Extra spacing between vertical sides and horizontal rows

    // Collect position groups
    let top_positions: Vec<_> = positions
        .iter()
        .filter(|p| matches!(p.side, Side::Top))
        .collect();
    let bottom_positions: Vec<_> = positions
        .iter()
        .filter(|p| matches!(p.side, Side::Bottom))
        .collect();
    let left_lower_positions: Vec<_> = positions
        .iter()
        .filter(|p| matches!(p.side, Side::LeftLower))
        .collect();
    let left_upper_positions: Vec<_> = positions
        .iter()
        .filter(|p| matches!(p.side, Side::LeftUpper))
        .collect();
    let right_upper_positions: Vec<_> = positions
        .iter()
        .filter(|p| matches!(p.side, Side::RightUpper))
        .collect();
    let right_lower_positions: Vec<_> = positions
        .iter()
        .filter(|p| matches!(p.side, Side::RightLower))
        .collect();

    // Calculate maximum indentation for left side
    let max_left_indent = left_lower_positions
        .iter()
        .enumerate()
        .map(|(i, _)| calculate_v_indentation(i, left_lower_positions.len()))
        .chain(
            left_upper_positions
                .iter()
                .enumerate()
                .map(|(i, _)| calculate_v_indentation(left_upper_positions.len() - 1 - i, left_upper_positions.len()))
        )
        .max()
        .unwrap_or(0);

    // Calculate maximum text width for left side players
    let max_left_text_width = left_lower_positions
        .iter()
        .chain(left_upper_positions.iter())
        .map(|pos| {
            let name_len = format_player_display_text(pos.player, false).len();
            let role_len = pos.player.role.len();
            name_len.max(role_len)
        })
        .max()
        .unwrap_or(0);

    // Top and bottom start after left side
    let horizontal_start_col = max_left_indent + max_left_text_width + SIDE_MARGIN;

    // Place top players
    for (i, pos) in top_positions.iter().enumerate() {
        let col = horizontal_start_col + i * PLAYER_SPACING;
        let row = 0;
        let name_text = format_player_display_text(pos.player, false);
        grid.add_cell(name_text, row, col);
        grid.add_cell(pos.player.role.clone(), row + 1, col);
    }

    // Calculate rightmost extent of top/bottom rows
    let max_horizontal_text_width = top_positions
        .iter()
        .chain(bottom_positions.iter())
        .map(|pos| {
            let name_len = format_player_display_text(pos.player, false).len();
            let role_len = pos.player.role.len();
            name_len.max(role_len)
        })
        .max()
        .unwrap_or(0);

    let max_horizontal_players = top_positions.len().max(bottom_positions.len());
    let horizontal_end_col = if max_horizontal_players > 0 {
        horizontal_start_col + (max_horizontal_players - 1) * PLAYER_SPACING + max_horizontal_text_width
    } else {
        horizontal_start_col
    };

    // Right side starts after horizontal rows
    let base_right_col = horizontal_end_col + SIDE_MARGIN;

    // Place right side players with V-shaped indentation
    let right_start_row = 3;

    // Right upper: receding from edge toward center (indentation increases away from apex)
    for (i, pos) in right_upper_positions.iter().enumerate() {
        let row = right_start_row + i * VERTICAL_SPACING;
        let indent = calculate_v_indentation(i, right_upper_positions.len());
        let col = base_right_col + indent;
        let name_text = format_player_display_text(pos.player, false);
        grid.add_cell(name_text, row, col);
        grid.add_cell(pos.player.role.clone(), row + 1, col);
    }

    // Right lower: extending from center back toward edge (indentation decreases away from apex)
    let right_lower_start_row = right_start_row + right_upper_positions.len() * VERTICAL_SPACING;
    for (i, pos) in right_lower_positions.iter().enumerate() {
        let row = right_lower_start_row + i * VERTICAL_SPACING;
        // For lower segment, apex is at beginning (i=0), so we reverse the indentation
        let indent = calculate_v_indentation(right_lower_positions.len() - 1 - i, right_lower_positions.len());
        let col = base_right_col + indent;
        let name_text = format_player_display_text(pos.player, false);
        grid.add_cell(name_text, row, col);
        grid.add_cell(pos.player.role.clone(), row + 1, col);
    }

    // Calculate bottom row based on vertical sides
    let max_vertical_players = (right_upper_positions.len() + right_lower_positions.len()).max(
        positions
            .iter()
            .filter(|p| matches!(p.side, Side::LeftLower | Side::LeftUpper))
            .count(),
    );
    let bottom_row = if max_vertical_players > 0 {
        right_start_row + max_vertical_players * VERTICAL_SPACING + 1
    } else {
        4 // Default if no vertical players
    };

    // Place bottom players
    for (i, pos) in bottom_positions.iter().enumerate() {
        let col = horizontal_start_col + i * PLAYER_SPACING;
        let name_text = format_player_display_text(pos.player, false);
        grid.add_cell(name_text, bottom_row, col);
        grid.add_cell(pos.player.role.clone(), bottom_row + 1, col);
    }

    // Place left side players with V-shaped indentation
    let base_left_col = 0;

    // Left lower: same slope direction as right lower
    for (i, pos) in left_lower_positions.iter().enumerate() {
        let row = right_start_row + i * VERTICAL_SPACING;
        let indent = calculate_v_indentation(i, left_lower_positions.len());
        let col = base_left_col + indent;
        let name_text = format_player_display_text(pos.player, false);
        grid.add_cell(name_text, row, col);
        grid.add_cell(pos.player.role.clone(), row + 1, col);
    }

    // Left upper: extending from edge toward center (same slope as left lower - positive)
    let left_upper_start_row = right_start_row + left_lower_positions.len() * VERTICAL_SPACING;
    for (i, pos) in left_upper_positions.iter().enumerate() {
        let row = left_upper_start_row + i * VERTICAL_SPACING;
        // Reverse indentation so it starts at edge and moves toward center (positive slope)
        let indent = calculate_v_indentation(left_upper_positions.len() - 1 - i, left_upper_positions.len());
        let col = base_left_col + indent;
        let name_text = format_player_display_text(pos.player, false);
        grid.add_cell(name_text, row, col);
        grid.add_cell(pos.player.role.clone(), row + 1, col);
    }

    let title = format!("Grimoire ({} players)", grimoire.players.len());
    render_grid_to_ascii(&grid, &title)
}

/// Render abstract grid to ASCII string with box drawing characters
fn render_grid_to_ascii(grid: &AbstractGrid, title: &str) -> String {
    let (width, height) = grid.dimensions();

    if width == 0 || height == 0 {
        return format!("┌─ {} ┐\n└────┘", title);
    }

    // Create a 2D array for the content
    let mut lines: Vec<Vec<char>> = vec![vec![' '; width]; height];

    // Fill in the cells
    for cell in &grid.cells {
        let row = cell.row - grid.min_row;
        let col_start = cell.col - grid.min_col;

        for (i, ch) in cell.content.chars().enumerate() {
            if col_start + i < width {
                lines[row][col_start + i] = ch;
            }
        }
    }

    // Build the output with borders
    let mut result = String::new();

    // Top border with title
    let title_section = format!("─ {} ", title);
    let border_width = width + 2; // +2 for the border characters
    let remaining = border_width.saturating_sub(title_section.len());
    result.push_str(&format!("┌{}{}┐\n", title_section, "─".repeat(remaining)));

    // Content lines
    for line in lines {
        result.push('│');
        result.extend(line);
        result.push('│');
        result.push('\n');
    }

    // Bottom border
    result.push_str(&format!("└{}┘", "─".repeat(border_width - 2)));

    result
}

#[allow(dead_code)]
fn format_bag(roles: &[Role]) -> String {
    if roles.is_empty() {
        return "{}".to_string();
    }

    let role_names: Vec<String> = roles
        .iter()
        .map(|r| r.name().to_lowercase().replace(' ', "_"))
        .collect();

    format!("{{{}}}", role_names.join(" "))
}

/// BotC SAT-based reasoning engine
#[derive(Parser, Debug)]
#[command(name = "botc-core")]
#[command(about = "Blood on the Clocktower SAT-based validator and reasoning engine", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Validate a role distribution bag
    ValidateRoleDistribution {
        /// Role bag in format: {role1 role2 role3 ...}
        bag: String,

        /// Optional script to restrict roles (e.g., "trouble-brewing", "tb")
        #[arg(short, long)]
        script: Option<String>,
    },

    /// Render grimoire as ASCII art
    RenderGrimoire {
        /// Grimoire in format: [Alice:baron Bob:imp Charlie:butler]
        grimoire: String,

        /// Turn configuration: top,ru,rl,bottom,ll,lu (e.g., "2,1,1,1,0,0")
        #[arg(short, long)]
        layout: Option<String>,
    },
}

// Macro for development tests - only shows message if tests are present
macro_rules! dev_tests {
    () => {
        // No tests - show nothing
    };
    ($($test:stmt)*) => {
        println!("\n=== Development Tests ===");
        println!("(These will be moved to #[test] when passing)\n");
        $($test)*
    };
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Some(Command::ValidateRoleDistribution { bag, script }) => {
            validate_role_distribution_cmd(&bag, script.as_deref());
        }
        Some(Command::RenderGrimoire { grimoire, layout }) => {
            render_grimoire_cmd(&grimoire, layout.as_deref());
        }
        None => {
            // No command given - run development tests
            println!("=== BotC Bag Legality Validator ===\n");
            println!("Run tests with: cargo test");
            println!("Run CLI with: cargo run -- <command>\n");
            println!("Available commands:");
            println!("  validate-role-distribution <bag>");
            println!("  render-grimoire <grimoire>");

            dev_tests! {
                // Uncomment to add development tests:
                // println!("Testing bag parsing...");
                // let bag = parse_bag("{chef imp}").unwrap();
                // println!("Parsed: {:?}", bag);
            }
        }
    }
}

fn render_grimoire_cmd(grimoire_str: &str, layout_str: Option<&str>) {
    // Parse grimoire
    let grimoire = match parse_grimoire(grimoire_str) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("Error parsing grimoire: {}", e);
            return;
        }
    };

    if grimoire.players.is_empty() {
        println!("Empty grimoire");
        return;
    }

    // Parse or generate layout
    let layout = if let Some(layout_str) = layout_str {
        match parse_layout_str(layout_str) {
            Ok(l) => l,
            Err(e) => {
                eprintln!("Error parsing layout: {}", e);
                return;
            }
        }
    } else {
        // Use a default layout: all players on top
        TurnBasedLayout {
            top_count: grimoire.players.len(),
            right_upper_count: 0,
            right_lower_count: 0,
            bottom_count: 0,
            left_lower_count: 0,
            left_upper_count: 0,
        }
    };

    // Verify layout matches player count
    let layout_total = layout.top_count
        + layout.right_upper_count
        + layout.right_lower_count
        + layout.bottom_count
        + layout.left_lower_count
        + layout.left_upper_count;

    if layout_total != grimoire.players.len() {
        eprintln!(
            "Error: Layout specifies {} players but grimoire has {}",
            layout_total,
            grimoire.players.len()
        );
        return;
    }

    // Render and print
    let rendered = render_grimoire_simple(&grimoire, &layout);
    println!("{}", rendered);
}

fn parse_layout_str(s: &str) -> Result<TurnBasedLayout, String> {
    let parts: Vec<&str> = s.split(',').map(|p| p.trim()).collect();
    if parts.len() != 6 {
        return Err(format!(
            "Layout must have 6 values (top,ru,rl,bottom,ll,lu), got {}",
            parts.len()
        ));
    }

    let parse_usize = |s: &str, name: &str| -> Result<usize, String> {
        s.parse::<usize>()
            .map_err(|_| format!("Invalid number for {}: '{}'", name, s))
    };

    Ok(TurnBasedLayout {
        top_count: parse_usize(parts[0], "top")?,
        right_upper_count: parse_usize(parts[1], "right_upper")?,
        right_lower_count: parse_usize(parts[2], "right_lower")?,
        bottom_count: parse_usize(parts[3], "bottom")?,
        left_lower_count: parse_usize(parts[4], "left_lower")?,
        left_upper_count: parse_usize(parts[5], "left_upper")?,
    })
}

struct DistributionAnalysis {
    base: RoleDistribution,
    expected: RoleDistribution,
    actual: RoleDistribution,
    modifiers: Vec<(String, SetupModifier)>, // (role_name, modifier)
}

fn analyze_distribution(player_count: u8, roles: &[Role]) -> DistributionAnalysis {
    let base = RoleDistribution::base_setup(player_count);

    // Calculate actual distribution from bag
    let mut actual = RoleDistribution {
        townsfolk: 0,
        outsider: 0,
        minion: 0,
        demon: 0,
    };
    for role in roles {
        match role.team() {
            Team::Townsfolk => actual.townsfolk += 1,
            Team::Outsider => actual.outsider += 1,
            Team::Minion => actual.minion += 1,
            Team::Demon => actual.demon += 1,
        }
    }

    // Apply modifiers to get expected distribution
    let mut expected = base.clone();
    let mut modifiers = Vec::new();

    for role in roles {
        if let Some(modifier) = role.setup_modifier() {
            modifiers.push((role.name().to_string(), modifier));
            match modifier {
                SetupModifier::AdjustCounts {
                    remove_townsfolk,
                    add_outsiders,
                } => {
                    expected.townsfolk = expected.townsfolk.saturating_sub(remove_townsfolk);
                    expected.outsider = expected.outsider.saturating_add(add_outsiders);
                }
            }
        }
    }

    DistributionAnalysis {
        base,
        expected,
        actual,
        modifiers,
    }
}

fn explain_distribution_error(analysis: &DistributionAnalysis) {
    println!("INVALID: This role distribution violates BotC setup rules\n");

    // Show the chain of reasoning
    println!(
        "  Base setup: {}T/{}O/{}M/{}D",
        analysis.base.townsfolk, analysis.base.outsider, analysis.base.minion, analysis.base.demon
    );

    if !analysis.modifiers.is_empty() {
        println!("  Setup modifications:");
        for (role_name, modifier) in &analysis.modifiers {
            match modifier {
                SetupModifier::AdjustCounts {
                    remove_townsfolk,
                    add_outsiders,
                } => {
                    println!(
                        "    {} adds {} Outsiders and removes {} Townsfolk",
                        role_name, add_outsiders, remove_townsfolk
                    );
                }
            }
        }
        println!(
            "  Required distribution: {}T/{}O/{}M/{}D",
            analysis.expected.townsfolk,
            analysis.expected.outsider,
            analysis.expected.minion,
            analysis.expected.demon
        );
    }

    println!(
        "  Your bag contains: {}T/{}O/{}M/{}D",
        analysis.actual.townsfolk,
        analysis.actual.outsider,
        analysis.actual.minion,
        analysis.actual.demon
    );

    // Show specific mismatches
    let mut problems = Vec::new();
    if analysis.actual.townsfolk != analysis.expected.townsfolk {
        let diff = analysis.expected.townsfolk as i16 - analysis.actual.townsfolk as i16;
        if diff > 0 {
            problems.push(format!("Missing {} Townsfolk", diff));
        } else {
            problems.push(format!("{} too many Townsfolk", -diff));
        }
    }
    if analysis.actual.outsider != analysis.expected.outsider {
        let diff = analysis.expected.outsider as i16 - analysis.actual.outsider as i16;
        if diff > 0 {
            problems.push(format!(
                "Missing {} Outsider{}",
                diff,
                if diff != 1 { "s" } else { "" }
            ));
        } else {
            problems.push(format!(
                "{} too many Outsider{}",
                -diff,
                if -diff != 1 { "s" } else { "" }
            ));
        }
    }
    if analysis.actual.minion != analysis.expected.minion {
        let diff = analysis.expected.minion as i16 - analysis.actual.minion as i16;
        if diff > 0 {
            problems.push(format!(
                "Missing {} Minion{}",
                diff,
                if diff != 1 { "s" } else { "" }
            ));
        } else {
            problems.push(format!(
                "{} too many Minion{}",
                -diff,
                if -diff != 1 { "s" } else { "" }
            ));
        }
    }
    if analysis.actual.demon != analysis.expected.demon {
        let diff = analysis.expected.demon as i16 - analysis.actual.demon as i16;
        if diff > 0 {
            problems.push(format!(
                "Missing {} Demon{}",
                diff,
                if diff != 1 { "s" } else { "" }
            ));
        } else {
            problems.push(format!(
                "{} too many Demon{}",
                -diff,
                if -diff != 1 { "s" } else { "" }
            ));
        }
    }

    if !problems.is_empty() {
        println!("\n  Problems:");
        for problem in problems {
            println!("    • {}", problem);
        }
    }
}

fn validate_role_distribution_cmd(bag_str: &str, script_name: Option<&str>) {
    // Load script if specified
    let script = if let Some(name) = script_name {
        match Script::from_name(name) {
            Some(s) => {
                println!("Using script: {}", s.title);
                Some(s)
            }
            None => {
                eprintln!("Error: Unknown script '{}'", name);
                eprintln!("Available scripts: trouble-brewing (tb)");
                std::process::exit(1);
            }
        }
    } else {
        None
    };

    println!("Validating role distribution: {}", bag_str);

    // Parse the bag spec (may contain placeholders)
    let specs = match parse_bag_spec_filtered(bag_str, script.as_ref()) {
        Ok(specs) => specs,
        Err(e) => {
            eprintln!("Error parsing bag: {}", e);
            std::process::exit(1);
        }
    };

    let player_count = specs.len() as u8;
    println!("  Player count: {}", player_count);

    // Check if there are any placeholders
    let has_placeholders = specs
        .iter()
        .any(|s| matches!(s, RoleSpec::Placeholder { .. }));

    // Show what we're solving for
    println!("  Roles specified:");
    for spec in &specs {
        match spec {
            RoleSpec::Known(role) => {
                println!("    - {} ({:?})", role.name(), role.team());
            }
            RoleSpec::Placeholder {
                name,
                team_constraint,
            } => {
                if let Some(team) = team_constraint {
                    println!("    - ?{}? (constrained to {:?})", name, team);
                } else {
                    println!("    - ?{}? (unconstrained)", name);
                }
            }
        }
    }

    // Encode with placeholders (works for both placeholder and non-placeholder cases)
    // Use environment variable to switch between encodings: BOTC_ENCODING=chain or BOTC_ENCODING=conditional
    let encoding_strategy = std::env::var("BOTC_ENCODING")
        .unwrap_or_else(|_| "conditional".to_string())
        .to_lowercase();

    let show_stats = std::env::var("BOTC_STATS").is_ok();

    let (vars, placeholders, slot_role_vars) = match encoding_strategy.as_str() {
        "chain" => {
            println!("Using CHAIN encoding strategy");
            encode_bag_spec_legality_chain_with_script(player_count, &specs, script.as_ref())
        }
        "conditional" => {
            println!("Using CONDITIONAL encoding strategy");
            encode_bag_spec_legality_with_script(player_count, &specs, script.as_ref())
        }
        _ => {
            eprintln!("Error: Invalid encoding strategy '{}'", encoding_strategy);

            // Suggest similar strategy using Jaro-Winkler similarity
            if encoding_strategy != "help" {
                let valid_strategies = ["conditional", "chain"];
                let mut max_similarity = 0.0;
                let mut suggestion = None;

                for &strategy in &valid_strategies {
                    let similarity = strsim::jaro_winkler(&encoding_strategy, strategy);
                    if similarity > max_similarity {
                        max_similarity = similarity;
                        suggestion = Some(strategy);
                    }
                }

                if let Some(suggested) = suggestion {
                    // Suggest if similarity is at least 60%
                    // This catches prefixes like "cond" -> "conditional"
                    if max_similarity >= 0.6 {
                        eprintln!("Did you mean '{}'?", suggested);
                    }
                }
            }

            eprintln!();
            eprintln!("Available encoding strategies:");
            eprintln!("  BOTC_ENCODING=conditional  - Conditional IF-THEN-ELSE encoding (default)");
            eprintln!(
                "  BOTC_ENCODING=chain        - Positional chain encoding (TypeScript-style)"
            );
            eprintln!();
            eprintln!(
                "Example: BOTC_ENCODING=chain cargo run -- validate-role-distribution '{{?role? imp}}'"
            );
            std::process::exit(1);
        }
    };

    // Keep a copy of role_present and slot variables before consuming vars.instance
    let _role_present_map = vars.role_present.clone();
    let slot_vars_copy = slot_role_vars.clone();

    // Collect statistics before consuming the instance
    let num_vars = vars.instance.n_vars();
    let num_clauses = vars.instance.n_clauses();

    if show_stats {
        println!("\n=== ENCODING STATISTICS ===");
        println!("  Variables: {}", num_vars);
        println!("  Clauses:   {}", num_clauses);
    }

    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(vars.instance.into_cnf().0).unwrap();

    let solve_start = std::time::Instant::now();
    let result = solver.solve().unwrap();
    let solve_time = solve_start.elapsed();

    if show_stats {
        println!("  Solve time: {:.3}ms", solve_time.as_secs_f64() * 1000.0);
    }

    println!("\n=== RESULT ===");
    match result {
        SolverResult::Sat => {
            println!(
                "✓ SATISFIABLE: Found valid role distribution for {} players",
                player_count
            );

            // Extract the complete solution from slot variables
            // This correctly handles multiple instances of the same role
            let present_roles: Result<Vec<Role>, String> = (|| {
                let mut roles_in_slots = Vec::new();
                for (slot_idx, _spec) in specs.iter().enumerate() {
                    // Find which role is assigned to this slot
                    let mut assigned_role = None;
                    for role in Role::all() {
                        let slot_lit = slot_vars_copy[slot_idx][role];
                        if let Ok(TernaryVal::True) = solver.lit_val(slot_lit) {
                            assigned_role = Some(*role);
                            break;
                        }
                    }

                    match assigned_role {
                        Some(role) => roles_in_slots.push(role),
                        None => {
                            return Err(format!("Slot {} has no role assigned", slot_idx));
                        }
                    }
                }
                Ok(roles_in_slots)
            })();

            match present_roles {
                Ok(present_roles) => {
                    println!("\n  Complete role distribution:");
                    for role in &present_roles {
                        println!("    - {} ({:?})", role.name(), role.team());
                    }

                    // Show placeholder assignments using slot variables
                    if !placeholders.is_empty() {
                        println!("\n  Placeholder assignments:");

                        for (slot_idx, spec) in specs.iter().enumerate() {
                            if let RoleSpec::Placeholder { name, .. } = spec {
                                // Find which role is assigned to this slot
                                let mut assigned_role = None;
                                for role in Role::all() {
                                    let slot_lit = slot_vars_copy[slot_idx][role];
                                    if let Ok(TernaryVal::True) = solver.lit_val(slot_lit) {
                                        assigned_role = Some(*role);
                                        break;
                                    }
                                }

                                match assigned_role {
                                    Some(role) => println!("    ?{}? = {}", name, role.name()),
                                    None => println!("    ?{}? = ERROR: no role assigned!", name),
                                }
                            }
                        }
                    }
                }
                Err(_e) => {
                    // Could not extract solution
                }
            }
            std::process::exit(0);
        }
        SolverResult::Unsat => {
            if !has_placeholders {
                // For non-placeholder case, show detailed error analysis
                let roles: Vec<Role> = specs
                    .iter()
                    .filter_map(|s| match s {
                        RoleSpec::Known(r) => Some(*r),
                        _ => None,
                    })
                    .collect();
                let analysis = analyze_distribution(player_count, &roles);
                explain_distribution_error(&analysis);
            } else {
                println!(
                    "✗ UNSATISFIABLE: No valid role distribution exists for the given constraints"
                );
            }
            std::process::exit(1);
        }
        SolverResult::Interrupted => {
            println!("\n=== RESULT ===");
            println!("ERROR: SAT solver was interrupted");
            std::process::exit(2);
        }
    }
}
