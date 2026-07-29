permit(
  principal,
  action,
  resource
) when {
  ((true && ((if ((ip("::5200:5f:3c45")).isInRange(ip("0.0.0.0"))) then principal else principal) in principal)) && false) && false
};
