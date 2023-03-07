const Type* SubTypeCheckNode::sub(const Type* sub_t, const Type* super_t) const {
  ciKlass* superk = super_t->is_klassptr()->klass();
  ciKlass* subk   = sub_t->isa_klassptr() ? sub_t->is_klassptr()->klass() : sub_t->is_oopptr()->klass();

  bool xsubk = sub_t->isa_klassptr() ? sub_t->is_klassptr()->klass_is_exact() : sub_t->is_oopptr()->klass_is_exact();


  // Oop can't be a subtype of abstract type that has no subclass.
  if (sub_t->isa_oopptr() && superk->is_instance_klass() &&
      !superk->is_interface() && superk->is_abstract() &&
      !superk->as_instance_klass()->has_subklass()) {
    Compile::current()->dependencies()->assert_leaf_type(superk);
    return TypeInt::CC_GT;
  }

  // Similar to logic in CmpPNode::sub()

  // Interfaces can't be trusted unless the subclass is an exact
  // interface (it can then only be a constant) or the subclass is an
  // exact array of interfaces (a newly allocated array of interfaces
  // for instance)
  if (superk && subk &&
      superk->is_loaded() && !superk->is_interface() &&
      subk->is_loaded() && (!subk->is_interface() || xsubk) &&
      (!superk->is_obj_array_klass() ||
       !superk->as_obj_array_klass()->base_element_klass()->is_interface()) &&
      (!subk->is_obj_array_klass() ||
       !subk->as_obj_array_klass()->base_element_klass()->is_interface() ||
       xsubk)) {
    bool unrelated_classes = false;
    if (superk->equals(subk)) {
      // skip
    } else if (superk->is_subtype_of(subk)) {
      // If the subclass is exact then the superclass is a subtype of
      // the subclass. Given they're no equals, that subtype check can
      // only fail.
      unrelated_classes = xsubk;
    } else if (subk->is_subtype_of(superk)) {
      // skip
    } else {
      // Neither class subtypes the other: they are unrelated and this
      // type check is known to fail.
      unrelated_classes = true;
    }
    if (unrelated_classes) {
      TypePtr::PTR jp = sub_t->is_ptr()->join_ptr(super_t->is_ptr()->_ptr);
      if (jp != TypePtr::Null && jp != TypePtr::BotPTR) {
        return TypeInt::CC_GT;
      }
    }
  }

  if (super_t->singleton()) {
    if (subk != NULL) {
      switch (Compile::current()->static_subtype_check(superk, subk)) {
      case Compile::SSC_always_false:
        return TypeInt::CC_GT;
      case Compile::SSC_always_true:
        return TypeInt::CC_EQ;
      case Compile::SSC_easy_test:
      case Compile::SSC_full_test:
        break;
      default:
        ShouldNotReachHere();
      }
    }
  }

  return bottom_type();
}
