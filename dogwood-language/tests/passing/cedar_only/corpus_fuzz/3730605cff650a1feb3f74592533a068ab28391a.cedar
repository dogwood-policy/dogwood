forbid(
  principal in a::"",
  action,
  resource
) when {
  (true && ((if ((ip("::7d:d87d:7d7d:2ff")).isMulticast()) then context else context)[""])) && false
};
