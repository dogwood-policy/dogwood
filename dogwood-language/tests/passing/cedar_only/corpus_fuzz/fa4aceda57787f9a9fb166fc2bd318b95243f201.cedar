forbid(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource == a::""
) when {
  (true && ((if ("" like "") then (if false then [[{}, {}, {}], [{}, {}, {}], [{}, {}, {}]] else [[{}, {}, {}], [{}, {}, {}], [{}, {}, {}]]) else [[{}, {}, {}], [{}, {}, {}], []]).containsAny([]))) && false
};
