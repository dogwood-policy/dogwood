forbid(
  principal,
  action in [M::Action::"action"],
  resource == M::a::""
) when {
  ((true && ((if (M::a::"" in M::a::"") then (if true then M::a::"" else M::a::"") else (if true then M::a::"" else M::a::"")) in (if (M::a::"" in M::a::"") then (if true then M::a::"" else M::a::"") else (if true then M::a::"" else M::a::"")))) && ((if (M::a::"" in M::a::"") then (if true then M::a::"" else M::a::"") else (if true then M::a::"" else M::a::"")) in (if (M::a::"" in M::a::"") then (if true then M::a::"" else M::a::"") else (if true then M::a::"" else M::a::"")))) && ((if (M::a::"" in M::a::"") then (if true then M::a::"" else M::a::"") else (if true then M::a::"" else M::a::"")) in (if (M::a::"" in M::a::"") then M::a::"" else resource))
};
