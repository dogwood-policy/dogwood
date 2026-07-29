forbid(
  principal in a::"\0\0\0\0\0\0\0",
  action in [],
  resource == a::"\0\0\0\0\0\0\0"
) when {
  true && ((if ("" like "") then (if false then ["V", ""] else ["\0\0\0", "", ""]) else [":"]).containsAny(if ("" like "") then (if true then [] else [[[[principal], []], []], [[[]], [], []], []]) else []))
};
