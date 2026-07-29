permit(
  principal,
  action,
  resource in a::"R"
) when {
  (true && ((if (if false then true else true) then ([context].contains({"": (datetime("1423-12-23")).offset(duration("422257545004419596660ms"))})) else (action in [a::"R"])) || (action in action))) && (action in action)
};
