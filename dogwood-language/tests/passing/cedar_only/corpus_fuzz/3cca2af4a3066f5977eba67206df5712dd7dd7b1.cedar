forbid(
  principal,
  action,
  resource
) when {
  (true && (a::"^^^" has "")) && (if (a::"^^^" has "") then (a::"^^^" has "") else (resource has ""))
};
