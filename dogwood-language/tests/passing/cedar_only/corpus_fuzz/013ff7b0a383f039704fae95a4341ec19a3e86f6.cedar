forbid(
  principal in a::"",
  action == Action::"action",
  resource == a::""
) when {
  ((true && ((if (a::"" in a::"") then (if true then principal else principal) else a::"") in (if (a::"" in a::"") then (if true then a::"" else a::"") else (if true then a::"" else a::"")))) && ((if (a::"" in a::"") then (if true then a::"" else a::"") else (if true then a::"" else a::"")) in (if (a::"" in a::"") then (if true then a::"" else a::"") else (if true then a::"" else a::"")))) && ((if (a::"" in a::"") then a::"" else a::"") in a::"")
};
