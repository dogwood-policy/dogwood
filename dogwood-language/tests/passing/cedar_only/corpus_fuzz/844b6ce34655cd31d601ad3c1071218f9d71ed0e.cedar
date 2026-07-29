permit(
  principal == r::"",
  action in [Action::"action"],
  resource
) when {
  true && ((if ([(datetime("1565-12-31T21:45:35-0429")).offset(duration("3255307777713450285d7306357454186664659h3255307777710489600s7306357454186664659ms"))].isEmpty()) then (context["\0"]) else (context["\0"])).isEmpty())
};
