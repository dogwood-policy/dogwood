@PR1Rx0("")
permit(
  principal == a::"",
  action in [Action::"\u{1d}"],
  resource is a in a::""
) when {
  ((true && ([context[""]].isEmpty())) && (principal in a::"")) && false
};
