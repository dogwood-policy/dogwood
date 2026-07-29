@r("Debian")
@z("")
permit(
  principal,
  action in [A::Action::""],
  resource == A::f::"\u{3}"
) when {
  false
};
