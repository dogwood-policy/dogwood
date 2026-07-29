permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && (context[""])) && (if (if true then ({"": a::""} has "") else ({"": a::""} has "")) then (context has "") else false)) && false
};
