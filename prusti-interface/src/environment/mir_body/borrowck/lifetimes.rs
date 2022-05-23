use crate::environment::{
    // borrowck::facts::{AllInputFacts, AllOutputFacts, BorrowckFacts, Loan, Point, Region},
    mir_dump::graphviz::{
         opaque_lifetime_string,
           ToText},
};
// use rustc_borrowck::consumers::{LocationTable, RichLocation};
use std::{
    cell::Ref,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};
use rustc_middle::mir;
use super::facts::{BorrowckFacts, AllInputFacts, Region, AllOutputFacts, Point, Loan, RichLocation};

pub struct Lifetimes {
    facts: BorrowckFacts,
}

impl Lifetimes {
    pub fn new(input_facts: &AllInputFacts, original_location_table: &rustc_borrowck::consumers::LocationTable) -> Self {
        let output_facts = polonius_engine::Output::compute(
            input_facts,
            polonius_engine::Algorithm::Naive,
            true,
        );
        let location_table = super::facts::LocationTable::new(original_location_table);
        Self {
            facts: BorrowckFacts::new(input_facts.clone(), output_facts, location_table),
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
        let subset_lifetimes: BTreeSet<Region> = self.facts.input_facts
            .subset_base
            .iter()
            .flat_map(|&(r1, r2, _)| [r1, r2])
            .collect();
        let subset_lifetimes_count: u32 = subset_lifetimes.len().try_into().unwrap();
        original_lifetimes_count + subset_lifetimes_count
    }

    // fn borrowck_in_facts(&self) -> Ref<AllInputFacts> {
    //     Ref::map(self.facts.input_facts.borrow(), |facts| {
    //         facts.as_ref().unwrap()
    //     })
    // }
    // fn borrowck_out_facts(&self) -> &AllOutputFacts {
    //     &self.output_facts
    // }
    // fn location_table(&self) -> Ref<LocationTable> {
    //     Ref::map(self.facts.location_table.borrow(), |table| {
    //         table.as_ref().unwrap()
    //     })
    // }
    // pub(super) fn debug_borrowck_in_facts(&self) {
    //     eprintln!("{:?}", self.borrowck_in_facts());
    // }
    // pub(super) fn debug_borrowck_out_facts(&self) {
    //     eprintln!("{:?}", self.borrowck_out_facts());
    // }
    pub(super) fn get_original_lifetimes(&self) -> Vec<Region> {
        self.facts.input_facts
            .loan_issued_at
            .iter()
            .map(|(region, _, _)| *region)
            .collect()
    }
    // pub(super) fn get_subset_base(&self, location: RichLocation) -> Vec<(Region, Region)> {
    //     let point = self.location_to_point(location);
    //     let borrowck_in_facts = self.borrowck_in_facts();
    //     borrowck_in_facts
    //         .subset_base
    //         .iter()
    //         .flat_map(|&(r1, r2, p)| if p == point { Some((r1, r2)) } else { None })
    //         .collect()
    // }
    fn location_to_point(&self, location: RichLocation) -> Point {
        self.facts.location_table.location_to_point(location)
    }
    // pub(super) fn get_subset(&self, location: RichLocation) -> BTreeMap<Region, BTreeSet<Region>> {
    //     let point = self.location_to_point(location);
    //     let borrowck_out_facts = self.borrowck_out_facts();
    //     if let Some(map) = borrowck_out_facts.subset.get(&point) {
    //         map.clone()
    //     } else {
    //         BTreeMap::new()
    //     }
    // }
    // pub(super) fn get_origin_live_on_entry(&self, location: RichLocation) -> Vec<Region> {
    //     let point = self.location_to_point(location);
    //     let borrowck_out_facts = self.borrowck_out_facts();
    //     if let Some(origins) = borrowck_out_facts.origin_live_on_entry.get(&point) {
    //         origins.clone()
    //     } else {
    //         Vec::new()
    //     }
    // }
    pub(super) fn get_loan_live_at(&self, location: RichLocation) -> Vec<Loan> {
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
