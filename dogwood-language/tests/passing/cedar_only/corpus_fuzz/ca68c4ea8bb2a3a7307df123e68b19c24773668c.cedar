forbid(
  principal in a::"",
  action in [Action::"\u{e}",Action::"\u{e}"],
  resource in a::""
) when {
  (true && ([[[ip("138.138.138.138"), ip("6464:464:6464:3a64:3ff:5b99:990e:3d24")], []], []] == [])) && false
};
