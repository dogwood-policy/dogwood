@A00000000("")
permit(
  principal is a in a::":",
  action in [Action::"action",Action::"action",Action::"action"],
  resource is a in a::":"
) when {
  ((true && (if (if (if true then true else true) then (action is a) else (action is a)) then ((if true then action else action) is a) else ((if true then action else action) is a))) && ((if (action is a) then (if false then action else action) else (if true then action else action)) is a)) && ((if (action is a) then a::":" else a::":") is a)
};
