forbid(
  principal in A::a::"",
  action in [A::Action::"action"],
  resource
) when {
  ((true && ([{":": {}}, {":": {}}, context].contains(if true then context else {":": {}}))) && false) && false
};
