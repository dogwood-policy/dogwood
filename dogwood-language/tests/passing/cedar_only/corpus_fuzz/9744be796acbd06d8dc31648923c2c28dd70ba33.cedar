forbid(
  principal in a::"",
  action,
  resource
) when {
  (true && ((if ((ip("::5b:ffff:5d5d:5d5d:5d5d")).isMulticast()) then context else context)[""])) && false
};
