permit(
  principal,
  action in [Action::"action"],
  resource in a::""
) when {
  (true && (if (if (if false then false else false) then (if false then true else false) else ([].contains([true, true]))) then false else false)) && false
};
