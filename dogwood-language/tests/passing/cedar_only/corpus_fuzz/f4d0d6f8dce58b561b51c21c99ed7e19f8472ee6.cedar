forbid(
  principal in a::"",
  action == Action::";~",
  resource in a::""
) when {
  (true && (["ng", resource.getTag("")].containsAny([]))) && false
};
