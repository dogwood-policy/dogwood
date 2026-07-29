permit(
  principal,
  action,
  resource
) when {
  (true && ((a::"" in (if true then principal else principal)) || ([].containsAny([])))) && ((if ({"": false}[""]) then (if false then {"": true} else context) else ({"": context}[""]))[""])
};
