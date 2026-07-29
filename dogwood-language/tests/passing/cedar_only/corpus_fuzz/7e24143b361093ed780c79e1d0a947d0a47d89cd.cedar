forbid(
  principal in a::"",
  action,
  resource
) when {
  (true && (({"": [[], [false]]}[""]) == [[true, false, false], [], []])) && false
};
