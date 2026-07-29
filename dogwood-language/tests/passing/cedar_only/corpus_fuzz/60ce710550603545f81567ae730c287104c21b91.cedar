permit(
  principal,
  action == A::Action::"action",
  resource == A::a::""
) when {
  ((true && ([{"": false, "00:": context}, context, context].contains(if true then {"": false, "00:": {}} else {"": false, "00:": {}}))) && false) && false
};
