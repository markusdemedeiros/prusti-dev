use crate::environment::mir_dump::graphviz::{opaque_lifetime_string, ToText};
// use rustc_borrowck::consumers::{LocationTable, RichLocation};
use super::facts::{
    AllInputFacts, AllOutputFacts, BorrowckFacts, Loan, LocationTable, Point, Region, RichLocation,
};
use rustc_middle::mir;
use std::{
    cell::Ref,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

pub struct Lifetimes {
    facts: BorrowckFacts,
}

impl Lifetimes {
    pub fn new(input_facts: AllInputFacts, location_table: LocationTable) -> Self {
        let output_facts =
            polonius_engine::Output::compute(&input_facts, polonius_engine::Algorithm::Naive, true);
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
    pub(in super::super) fn get_original_lifetimes(&self) -> Vec<Region> {
        self.facts
            .input_facts
            .loan_issued_at
            .iter()
            .map(|(region, _, _)| *region)
            .collect()
    }

    pub(in super::super) fn location_to_point(&self, location: RichLocation) -> Point {
        self.facts.location_table.location_to_point(location)
    }

    pub(in super::super) fn get_loan_live_at(&self, location: RichLocation) -> Vec<Loan> {
        let point = self.location_to_point(location);
        if let Some(loans) = self.facts.output_facts.loan_live_at.get(&point) {
            loans.clone()
        } else {
            Vec::new()
        }
    }
    pub(in super::super) fn get_origin_contains_loan_at(
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

mod graphviz {

    use crate::environment::mir_dump::graphviz::{
        opaque_lifetime_string,
        to_text::{loan_to_text, to_sorted_text},
        ToText,
    };
    // use rustc_borrowck::consumers::{LocationTable, RichLocation};
    use super::{
        super::facts::{
            AllInputFacts, AllOutputFacts, BorrowckFacts, Loan, LocationTable, Point, Region,
            RichLocation,
        },
        Lifetimes,
    };
    use rustc_middle::mir;
    use std::{
        cell::Ref,
        collections::{BTreeMap, BTreeSet},
        rc::Rc,
    };

    pub struct LifetimeWithInclusions {
        lifetime: Region,
        loan: Loan,
        included_in: Vec<Region>,
    }

    impl super::graphviz::ToText for LifetimeWithInclusions {
        fn to_text(&self) -> String {
            let lifetimes = to_sorted_text(&self.included_in);
            format!(
                "{} ⊑ {} ({})",
                self.lifetime.to_text(),
                lifetimes.join(" ⊓ "),
                loan_to_text(&self.loan)
            )
        }
    }

    /// Functionality used only for the Graphviz output.
    pub trait LifetimesGraphviz {
        fn get_opaque_lifetimes_with_inclusions(&self) -> Vec<LifetimeWithInclusions>;
        fn get_subset_base(&self, location: RichLocation) -> Vec<(Region, Region)>;
        fn get_subset(&self, location: RichLocation) -> BTreeMap<Region, BTreeSet<Region>>;
        fn get_origin_live_on_entry(&self, location: RichLocation) -> Vec<Region>;
    }

    impl LifetimesGraphviz for Lifetimes {
        fn get_opaque_lifetimes_with_inclusions(&self) -> Vec<LifetimeWithInclusions> {
            let mut opaque_lifetimes = Vec::new();
            for &(placeholder, loan) in &self.facts.input_facts.placeholder {
                let mut included_in = Vec::new();
                for &(r1, r2) in &self.facts.input_facts.known_placeholder_subset {
                    if r1 == placeholder {
                        included_in.push(r2);
                    }
                }
                opaque_lifetimes.push(LifetimeWithInclusions {
                    lifetime: placeholder,
                    loan,
                    included_in,
                });
            }
            opaque_lifetimes
        }

        fn get_subset_base(&self, location: RichLocation) -> Vec<(Region, Region)> {
            let point = self.location_to_point(location);
            self.facts
                .input_facts
                .subset_base
                .iter()
                .flat_map(|&(r1, r2, p)| if p == point { Some((r1, r2)) } else { None })
                .collect()
        }

        fn get_subset(&self, location: RichLocation) -> BTreeMap<Region, BTreeSet<Region>> {
            let point = self.location_to_point(location);
            if let Some(map) = self.facts.output_facts.subset.get(&point) {
                map.clone()
            } else {
                BTreeMap::new()
            }
        }

        fn get_origin_live_on_entry(&self, location: RichLocation) -> Vec<Region> {
            let point = self.location_to_point(location);
            if let Some(origins) = self.facts.output_facts.origin_live_on_entry.get(&point) {
                origins.clone()
            } else {
                Vec::new()
            }
        }
    }
}

pub use self::graphviz::LifetimesGraphviz;
