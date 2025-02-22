// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    common::identifier::WithIdentifier, converter::type_substitution::Generic, polymorphic::ast::*,
};
use rustc_hash::{FxHashMap, FxHasher};
use std::{
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    mem::discriminant,
};

/// The identifier of a statement. Used in error reporting.
/// TODO: This should probably have custom `PartialEq, Eq, Hash, PartialOrd, Ord` impls,
/// to ensure that it is not included in these calculations.
#[derive(
    Debug, Copy, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize, PartialOrd, Ord,
)]
pub struct Position {
    pub(crate) line: i32,
    pub(crate) column: i32,
    pub(crate) id: u64,
}

impl Position {
    pub fn new(line: i32, column: i32, id: u64) -> Self {
        Position { line, column, id }
    }
}

impl Default for Position {
    fn default() -> Self {
        Position::new(0, 0, 0)
    }
}

pub enum PermAmountError {
    InvalidAdd(PermAmount, PermAmount),
    InvalidSub(PermAmount, PermAmount),
}

/// The permission amount.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum PermAmount {
    Read,
    Write,
    /// The permission remaining after ``Read`` was subtracted from ``Write``.
    Remaining,
}

impl PermAmount {
    /// Can this permission amount be used in specifications?
    pub fn is_valid_for_specs(&self) -> bool {
        match self {
            PermAmount::Read | PermAmount::Write => true,
            PermAmount::Remaining => false,
        }
    }
}

impl std::ops::Add for PermAmount {
    type Output = Result<PermAmount, PermAmountError>;
    fn add(self, other: PermAmount) -> Self::Output {
        match (self, other) {
            (PermAmount::Read, PermAmount::Remaining)
            | (PermAmount::Remaining, PermAmount::Read) => Ok(PermAmount::Write),
            _ => Err(PermAmountError::InvalidAdd(self, other)),
        }
    }
}

impl std::ops::Sub for PermAmount {
    type Output = Result<PermAmount, PermAmountError>;
    fn sub(self, other: PermAmount) -> Result<PermAmount, PermAmountError> {
        match (self, other) {
            (PermAmount::Write, PermAmount::Read) => Ok(PermAmount::Remaining),
            (PermAmount::Write, PermAmount::Remaining) => Ok(PermAmount::Read),
            _ => Err(PermAmountError::InvalidSub(self, other)),
        }
    }
}

impl fmt::Display for PermAmount {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PermAmount::Read => write!(f, "read"),
            PermAmount::Write => write!(f, "write"),
            PermAmount::Remaining => write!(f, "write-read"),
        }
    }
}

#[allow(clippy::incorrect_partial_ord_impl_on_ord_type)]
impl PartialOrd for PermAmount {
    fn partial_cmp(&self, other: &PermAmount) -> Option<Ordering> {
        match (self, other) {
            (PermAmount::Read, PermAmount::Write) => Some(Ordering::Less),
            (PermAmount::Read, PermAmount::Read) | (PermAmount::Write, PermAmount::Write) => {
                Some(Ordering::Equal)
            }
            (PermAmount::Write, PermAmount::Read) => Some(Ordering::Greater),
            _ => None,
        }
    }
}

impl Ord for PermAmount {
    fn cmp(&self, other: &PermAmount) -> Ordering {
        self.partial_cmp(other)
            .unwrap_or_else(|| panic!("Undefined comparison between {:?} and {:?}", self, other))
    }
}

#[derive(
    Debug, Clone, serde::Serialize, serde::Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord,
)]
pub enum Float {
    F32,
    F64,
}

#[derive(
    Debug, Clone, Copy, serde::Serialize, serde::Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord,
)]
pub enum BitVectorSize {
    BV8,
    BV16,
    BV32,
    BV64,
    BV128,
}

impl fmt::Display for BitVectorSize {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BitVectorSize::BV8 => write!(f, "BV8"),
            BitVectorSize::BV16 => write!(f, "BV16"),
            BitVectorSize::BV32 => write!(f, "BV32"),
            BitVectorSize::BV64 => write!(f, "BV64"),
            BitVectorSize::BV128 => write!(f, "BV128"),
        }
    }
}

impl From<usize> for BitVectorSize {
    fn from(value: usize) -> Self {
        match value {
            8 => BitVectorSize::BV8,
            16 => BitVectorSize::BV16,
            32 => BitVectorSize::BV32,
            64 => BitVectorSize::BV64,
            128 => BitVectorSize::BV128,
            _ => panic!("Invalid bitvector size: {}", value),
        }
    }
}

#[derive(
    Debug, Clone, Copy, serde::Serialize, serde::Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord,
)]
pub enum BitVector {
    Signed(BitVectorSize),
    Unsigned(BitVectorSize),
}

impl fmt::Display for BitVector {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Signed(value) => write!(f, "S{}", value),
            Self::Unsigned(value) => write!(f, "U{}", value),
        }
    }
}

#[derive(
    Debug, Clone, serde::Serialize, serde::Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord,
)]
pub enum Type {
    Int,
    Bool,
    Float(Float),
    BitVector(BitVector),
    Seq(SeqType),
    Map(MapType),
    /// A raw Viper reference
    Ref,
    /// TypedRef: the first parameter is the name of the predicate that encodes the type
    TypedRef(TypedRef),
    Domain(DomainType),
    Snapshot(SnapshotType),
    // For type substitution
    TypeVar(TypeVar),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Bool => write!(f, "Bool"),
            Type::Ref => write!(f, "Ref"),
            Type::Float(Float::F32) => write!(f, "F32"),
            Type::Float(Float::F64) => write!(f, "F64"),
            Type::BitVector(value) => write!(f, "{}", value),
            Type::Seq(seq) => seq.fmt(f),
            Type::Map(map) => map.fmt(f),
            Type::TypedRef(_) => write!(f, "Ref({})", self.encode_as_string()),
            Type::Domain(_) => write!(f, "Domain({})", self.encode_as_string()),
            Type::Snapshot(_) => write!(f, "Snapshot({})", self.encode_as_string()),
            Type::TypeVar(type_var) => type_var.fmt(f),
        }
    }
}

impl Type {
    pub fn is_typed_ref_or_type_var(&self) -> bool {
        self.is_typed_ref() || self.is_type_var()
    }

    pub fn is_typed_ref(&self) -> bool {
        matches!(self, &Type::TypedRef(_))
    }

    pub fn is_domain(&self) -> bool {
        matches!(self, &Type::Domain(_))
    }

    pub fn is_snapshot(&self) -> bool {
        matches!(self, &Type::Snapshot(_))
    }

    pub fn is_seq(&self) -> bool {
        matches!(self, &Type::Seq(_))
    }

    pub fn is_map(&self) -> bool {
        matches!(self, &Type::Map(_))
    }

    pub fn is_type_var(&self) -> bool {
        matches!(self, &Type::TypeVar(_))
    }

    pub fn is_mir_reference(&self) -> bool {
        if let Type::TypedRef(TypedRef { label, .. }) = self {
            // FIXME: We should not rely on string names for type conversions.
            label == "ref"
        } else {
            false
        }
    }

    pub fn name(&self) -> String {
        match self {
            Type::Bool => "bool".to_string(),
            Type::Int => "int".to_string(),
            Type::Ref => "ref".to_string(),
            Type::Float(Float::F32) => "f32".to_string(),
            Type::Float(Float::F64) => "f64".to_string(),
            Type::BitVector(value) => value.to_string(),
            Type::Domain(_)
            | Type::Snapshot(_)
            | Type::TypedRef(_)
            | Type::TypeVar(_)
            | Type::Seq(_)
            | Type::Map(..) => self.encode_as_string(),
        }
    }

    /// Construct a new VIR type that corresponds to an enum variant.
    #[must_use]
    pub fn variant(self, variant: &str) -> Self {
        match self {
            Type::TypedRef(mut typed_ref) => {
                typed_ref.variant = variant.into();
                Type::TypedRef(typed_ref)
            }
            _ => unreachable!(),
        }
    }

    /// Replace all generic types with their instantiations by using string substitution.
    #[must_use]
    pub fn patch(self, substs: &FxHashMap<TypeVar, Type>) -> Self {
        self.substitute(substs)
    }

    pub fn typed_ref<S: Into<String>>(name: S) -> Self {
        Type::TypedRef(TypedRef {
            label: name.into(),
            arguments: vec![],
            variant: String::from(""),
        })
    }

    pub fn typed_ref_with_args<S: Into<String>>(name: S, arguments: Vec<Type>) -> Self {
        Type::TypedRef(TypedRef {
            label: name.into(),
            arguments,
            variant: String::from(""),
        })
    }

    pub fn domain<S: Into<String>>(name: S) -> Self {
        Type::Domain(DomainType {
            label: name.into(),
            arguments: vec![],
            variant: String::from(""),
        })
    }

    pub fn domain_with_args<S: Into<String>>(name: S, arguments: Vec<Type>) -> Self {
        Type::Domain(DomainType {
            label: name.into(),
            arguments,
            variant: String::from(""),
        })
    }

    pub fn snapshot<S: Into<String>>(name: S) -> Self {
        Type::Snapshot(SnapshotType {
            label: name.into(),
            arguments: vec![],
            variant: String::from(""),
        })
    }

    pub fn snapshot_with_args<S: Into<String>>(name: S, arguments: Vec<Type>) -> Self {
        Type::Snapshot(SnapshotType {
            label: name.into(),
            arguments,
            variant: String::from(""),
        })
    }

    // TODO: this is a temporary solution for converting the encoded type in type encoder as a snapshot variant, which ould be cleaner
    #[must_use]
    pub fn convert_to_snapshot(&self) -> Self {
        match self {
            Type::TypedRef(typed_ref) => Type::Snapshot(typed_ref.clone().into()),
            Type::TypeVar(_) => Type::Snapshot(SnapshotType {
                label: self.encode_as_string(),
                arguments: Vec::new(),
                variant: String::from(""),
            }),
            _ => unreachable!(),
        }
    }

    pub fn type_var<S: Into<String>>(name: S) -> Self {
        Type::TypeVar(TypeVar { label: name.into() })
    }

    pub fn get_type_var(&self) -> Option<TypeVar> {
        if let Type::TypeVar(type_var) = self {
            Some(type_var.clone())
        } else {
            None
        }
    }

    pub fn get_id(&self) -> TypeId {
        match self {
            Type::Bool => TypeId::Bool,
            Type::Int => TypeId::Int,
            Type::Ref => TypeId::Ref,
            Type::Float(_) => TypeId::Float,
            Type::BitVector(_) => TypeId::BitVector,
            Type::TypedRef(_) => TypeId::Ref,
            Type::Domain(_) => TypeId::Domain,
            Type::Snapshot(_) => TypeId::Snapshot,
            Type::Seq(_) => TypeId::Seq,
            Type::Map(..) => TypeId::Map,
            Type::TypeVar(t) => unreachable!("{}", t),
        }
    }

    pub fn encode_as_string(&self) -> String {
        match self {
            Type::TypedRef(TypedRef {
                label,
                arguments,
                variant,
            })
            | Type::Domain(DomainType {
                label,
                arguments,
                variant,
            })
            | Type::Snapshot(SnapshotType {
                label,
                arguments,
                variant,
            }) => {
                let label_str = label.as_str();
                match label_str {
                    "ref" | "raw_ref" | "Slice" => {
                        format!("{}${}", label_str, Self::encode_arguments(arguments))
                    }
                    // TODO: remove len constraint once encoders are all updated with polymorphic
                    array if array.starts_with("Array") && !arguments.is_empty() => {
                        format!("{}${}", label_str, Self::encode_arguments(arguments))
                    }
                    "tuple" => format!(
                        "tuple{}${}",
                        arguments.len(),
                        Self::encode_arguments(arguments)
                    ),
                    // TODO: remove len constraint once encoders are all updated with polymorphic
                    closure if closure.starts_with("closure") && !arguments.is_empty() => format!(
                        "{}${}${}",
                        closure,
                        arguments.len(),
                        Self::hash_arguments(arguments)
                    ),
                    adt if adt.starts_with("enum") => format!(
                        "{}${}{}",
                        &adt[5..],
                        Self::encode_substs(arguments),
                        variant
                    ),
                    adt if adt.starts_with("adt") => format!(
                        "{}${}{}",
                        &adt[4..],
                        Self::encode_substs(arguments),
                        variant
                    ),
                    _label => {
                        if !arguments.is_empty() {
                            // Projection
                            format!("{}${}", label_str, Self::encode_arguments(arguments))
                        } else {
                            // General cases (e.g. bool, isize, never, ...)
                            String::from(label_str)
                        }
                    }
                }
            }
            Type::Seq(SeqType { box typ }) => {
                format!("Seq${}", Self::encode_arguments(&[typ.clone()]))
            }
            Type::Map(MapType {
                box key_type,
                box val_type,
            }) => {
                format!(
                    "Map${}${}",
                    Self::encode_arguments(&[key_type.clone()]),
                    Self::encode_arguments(&[val_type.clone()])
                )
            }
            Type::TypeVar(TypeVar { label }) => {
                assert!(
                    TypeVar::is_valid_label(label),
                    "Label {} is not valid",
                    label
                );
                format!("__TYPARAM__$_{}$__", label)
            }
            x => unreachable!("{}", x),
        }
    }

    /// The string to be appended to the encoding of certain types to make generics "less fragile".
    fn encode_substs(types: &[Type]) -> String {
        let mut composed_name = vec![
            "_beg_".to_string(), // makes generics "less fragile"
        ];
        let mut first = true;
        for typ in types.iter() {
            if first {
                first = false
            } else {
                // makes generics "less fragile"
                composed_name.push("_sep_".to_string());
            }
            composed_name.push(typ.encode_as_string());
        }
        composed_name.push("_end_".to_string()); // makes generics "less fragile"
        composed_name.join("$")
    }

    /// Converts vector of arguments to string connected with "$".
    fn encode_arguments(args: &[Type]) -> String {
        let mut composed_name = vec![];

        for arg in args.iter() {
            composed_name.push(arg.encode_as_string());
        }

        composed_name.join("$")
    }

    fn hash_arguments(args: &[Type]) -> u64 {
        let mut s = FxHasher::default();
        args.hash(&mut s);
        s.finish()
    }
}

use crate::common::display;

#[derive(
    Debug, Clone, serde::Serialize, serde::Deserialize, PartialOrd, Ord, PartialEq, Eq, Hash,
)]
pub struct SeqType {
    pub typ: Box<Type>,
}

impl fmt::Display for SeqType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Seq[{}]", &self.typ)
    }
}

#[derive(
    Debug, Clone, serde::Serialize, serde::Deserialize, PartialOrd, Ord, PartialEq, Eq, Hash,
)]
pub struct MapType {
    pub key_type: Box<Type>,
    pub val_type: Box<Type>,
}

impl fmt::Display for MapType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Map[{}, {}]", &self.key_type, &self.val_type)
    }
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct TypedRef {
    pub label: String,
    pub arguments: Vec<Type>,
    pub variant: String,
}

impl TypedRef {
    pub fn new<S: Into<String>>(label: S, arguments: Vec<Type>) -> Self {
        Self {
            label: label.into(),
            arguments,
            variant: String::from(""),
        }
    }
}

impl PartialEq for TypedRef {
    fn eq(&self, other: &Self) -> bool {
        (&self.label, &self.arguments, &self.variant)
            == (&other.label, &other.arguments, &other.variant)
    }
}

impl Eq for TypedRef {}

impl Hash for TypedRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.label, &self.arguments, &self.variant).hash(state);
    }
}

impl From<SnapshotType> for TypedRef {
    fn from(snapshot: SnapshotType) -> Self {
        Self {
            label: snapshot.label,
            arguments: snapshot.arguments,
            variant: snapshot.variant,
        }
    }
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct DomainType {
    pub label: String,
    pub arguments: Vec<Type>,
    pub variant: String,
}

impl PartialEq for DomainType {
    fn eq(&self, other: &Self) -> bool {
        (&self.label, &self.arguments) == (&other.label, &other.arguments)
    }
}

impl Eq for DomainType {}

impl Hash for DomainType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.label, &self.arguments).hash(state);
    }
}

impl From<TypedRef> for DomainType {
    fn from(typed_ref: TypedRef) -> DomainType {
        DomainType {
            label: typed_ref.label,
            arguments: typed_ref.arguments,
            variant: typed_ref.variant,
        }
    }
}

impl From<TypeVar> for DomainType {
    fn from(type_var: TypeVar) -> DomainType {
        DomainType {
            label: type_var.label,
            arguments: vec![],
            variant: String::from(""),
        }
    }
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct SnapshotType {
    pub label: String,
    pub arguments: Vec<Type>,
    pub variant: String,
}

impl PartialEq for SnapshotType {
    fn eq(&self, other: &Self) -> bool {
        (&self.label, &self.arguments) == (&other.label, &other.arguments)
    }
}

impl Eq for SnapshotType {}

impl Hash for SnapshotType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.label, &self.arguments).hash(state);
    }
}

impl From<TypedRef> for SnapshotType {
    fn from(typed_ref: TypedRef) -> SnapshotType {
        SnapshotType {
            label: typed_ref.label,
            arguments: typed_ref.arguments,
            variant: typed_ref.variant,
        }
    }
}

impl From<TypeVar> for SnapshotType {
    fn from(type_var: TypeVar) -> SnapshotType {
        SnapshotType {
            label: type_var.label,
            arguments: vec![],
            variant: String::from(""),
        }
    }
}

#[derive(
    Debug, Clone, serde::Serialize, serde::Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord,
)]
pub struct TypeVar {
    pub label: String,
}

impl TypeVar {
    pub fn is_valid_label(label: &str) -> bool {
        !label.contains(' ') && !label.contains('<') && !label.contains('>') && !label.contains('=')
    }
}

impl fmt::Display for TypeVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TypeVar({})", &self.label)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum TypeId {
    Int,
    Bool,
    Float,
    BitVector,
    Ref,
    Seq,
    Map,
    Domain,
    Snapshot,
}

#[derive(Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct LocalVar {
    pub name: String,
    pub typ: Type,
}

impl fmt::Display for LocalVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl fmt::Debug for LocalVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.name, self.typ)
    }
}

impl LocalVar {
    pub fn new<S: Into<String>>(name: S, typ: Type) -> Self {
        LocalVar {
            name: name.into(),
            typ,
        }
    }
}

#[derive(Clone, Eq, PartialEq, Hash, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct Field {
    pub name: String,
    pub typ: Type,
}

impl fmt::Display for Field {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl fmt::Debug for Field {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.name, self.typ)
    }
}

impl Field {
    pub fn new<S: Into<String>>(name: S, typ: Type) -> Self {
        Field {
            name: name.into(),
            typ,
        }
    }

    pub fn typed_ref_name(&self) -> Option<String> {
        match self.typ {
            Type::TypedRef(_) | Type::TypeVar(_) => Some(self.typ.encode_as_string()),
            _ => None,
        }
    }
}

impl WithIdentifier for Field {
    fn get_identifier(&self) -> String {
        self.name.clone()
    }
}
