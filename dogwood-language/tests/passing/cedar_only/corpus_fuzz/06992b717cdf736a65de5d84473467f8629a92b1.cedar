@AXXX00A("")
@AXXXXXX("")
forbid(
  principal is A000000vW,
  action == Action::"",
  resource
) when {
  true && ((if true then (A000000vW::";".getTag("")) else (A000000vW::"".getTag(""))).isIpv6())
};
