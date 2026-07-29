permit(
  principal in a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  (true && ([].contains((if true then {l: [[[true, true, true], [true, false, false], [false, false]], [[false, true], [true, true]], [[], [true, false, false]]]} else {l: [[], []]}).l))) && false
};
