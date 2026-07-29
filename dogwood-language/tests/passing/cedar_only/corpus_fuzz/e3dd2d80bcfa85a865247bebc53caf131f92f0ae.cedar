permit(
  principal,
  action in [Action::"-"],
  resource
) when {
  true && ((if ([(datetime("1675-11-09")).offset(duration("7405841751649090415h2709026936m"))].isEmpty()) then [] else []).isEmpty())
};
