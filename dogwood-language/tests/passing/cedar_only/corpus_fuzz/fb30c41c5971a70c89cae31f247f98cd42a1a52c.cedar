permit(
  principal,
  action,
  resource in a::"<\n\0\0\0\0"
) when {
  (true && ((if ([[a::"<\n\0\0\0\0", action, a::"<\n\0\0\0\0"], [a::"<\n\0\0\0\0", a::"<\n\0\0\0\0", a::"<\n\0\0\0\0"], [a::"<\n\0\0\0\0", resource, principal]].containsAny([false, false])) then (if false then [{"": ""}, {"": ""}] else [{"": ""}, {"": ""}]) else (if false then [{"": ""}, {"": ""}] else [{"": ""}, context])).containsAny([[], []]))) && false
};
