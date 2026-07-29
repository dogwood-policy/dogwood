@Q("")
forbid(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  ((true && ("{{principaE\0\0\0{{{\0\0\0{{S{SSS" like "*S**")) && ((("{{principaE\0\0\0{{{\0\0\0{{S{SSS" like "S\0*\0") || ("{{principaE\0\0\0{{{\0\0\0{{S{SSS" like "*S**\0")) || ("{{principaE\0\0\0{{{\0\0\0{{S{SSS" like "*S*\0*\0"))) && false
};
