use super::facts::{
    AllInputFacts, BorrowckFacts, Loan, LocationTable, Point, Region, RichLocation,
};
use crate::environment::debug_utils::to_text::{opaque_lifetime_string, ToText};
use rustc_middle::mir;
use std::collections::{BTreeMap, BTreeSet};

mod graphviz;

pub use self::graphviz::LifetimesGraphviz;

pub struct Lifetimes {
    facts: BorrowckFacts,
}

impl Lifetimes {
    pub fn new(input_facts: AllInputFacts, location_table: LocationTable) -> Self {
        let output_facts =
            polonius_engine::Output::compute(&input_facts, polonius_engine::Algorithm::Naive, true);
        Self {
            facts: BorrowckFacts::new(input_facts, output_facts, location_table),
        }
    }

    pub fn get_loan_live_at_start(&self, location: mir::Location) -> BTreeSet<String> {
        let info = self.get_loan_live_at(RichLocation::Start(location));
        info.into_iter()
            .map(|x| opaque_lifetime_string(x.index()))
            .collect()
    }

    pub fn get_origin_contains_loan_at_mid(
        &self,
        location: mir::Location,
    ) -> BTreeMap<String, BTreeSet<String>> {
        let info = self.get_origin_contains_loan_at(RichLocation::Mid(location));
        info.iter()
            .map(|(k, v)| {
                (
                    k.to_text(),
                    v.iter()
                        .map(|x| opaque_lifetime_string(x.index()))
                        .collect(),
                )
            })
            .collect()
    }

    pub fn lifetime_count(&self) -> u32 {
        let original_lifetimes_count: u32 = self.get_original_lifetimes().len().try_into().unwrap();
        let subset_lifetimes: BTreeSet<Region> = self
            .facts
            .input_facts
            .subset_base
            .iter()
            .flat_map(|&(r1, r2, _)| [r1, r2])
            .collect();
        let subset_lifetimes_count: u32 = subset_lifetimes.len().try_into().unwrap();
        original_lifetimes_count + subset_lifetimes_count
    }

    fn get_original_lifetimes(&self) -> Vec<Region> {
        self.facts
            .input_facts
            .loan_issued_at
            .iter()
            .map(|(region, _, _)| *region)
            .collect()
    }

    fn location_to_point(&self, location: RichLocation) -> Point {
        self.facts.location_table.location_to_point(location)
    }

    fn get_loan_live_at(&self, location: RichLocation) -> Vec<Loan> {
        let point = self.location_to_point(location);
        if let Some(loans) = self.facts.output_facts.loan_live_at.get(&point) {
            loans.clone()
        } else {
            Vec::new()
        }
    }

    fn get_origin_contains_loan_at(
        &self,
        location: RichLocation,
    ) -> BTreeMap<Region, BTreeSet<Loan>> {
        let point = self.location_to_point(location);
        if let Some(map) = self.facts.output_facts.origin_contains_loan_at.get(&point) {
            map.clone()
        } else {
            BTreeMap::new()
        }
    }
}
