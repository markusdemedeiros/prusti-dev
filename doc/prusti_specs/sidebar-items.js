initSidebarItems({"enum":[["ExternSpecKind",""],["SpecAttributeKind","This type identifies one of the procedural macro attributes of Prusti"]],"fn":[["body_invariant",""],["closure","Unlike the functions above, which are only called from prusti-contracts-internal, this function also needs to be called from prusti-contracts-impl, because we still need to parse the macro in order to replace it with the closure definition. Therefore, there is an extra parameter drop_spec here which tells the function whether to keep the specification (for -internal) or drop it (for -impl)."],["extern_spec",""],["invariant",""],["predicate",""],["refine_trait_spec",""],["rewrite_prusti_attributes","Rewrite an item as required by all its specification attributes."],["type_model",""]],"macro":[["parse_quote_spanned","Same as `parse_quote!`, but applies a given span to all tokens originating within the macro invocation."]],"mod":[["specifications",""]]});