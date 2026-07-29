permit(
  principal,
  action,
  resource == a::""
) when {
  ((true && ((if ((ip("229.229.0.255/6")).isInRange(ip("8787:8787:8787:8787:8787:8787:8787:8787/6"))) then (decimal("0.0")) else (decimal("0.0"))) == false)) && false) && false
};
