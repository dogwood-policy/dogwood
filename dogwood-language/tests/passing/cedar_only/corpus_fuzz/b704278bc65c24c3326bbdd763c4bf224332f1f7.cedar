permit(
  principal,
  action,
  resource
) when {
  ((true && ((if ((ip("255.255.255.255/24")).isIpv4()) then (ip("0.0.0.0")) else (ip("0.0.0.0"))).isMulticast())) && false) && false
};
