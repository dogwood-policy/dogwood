forbid(
  principal,
  action,
  resource
) when {
  (true && ((if (["", ""].containsAll([false, false, false])) then context else context)[""])) && false
};
