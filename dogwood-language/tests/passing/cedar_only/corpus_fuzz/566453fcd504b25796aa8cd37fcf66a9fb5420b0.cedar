permit(
  principal,
  action,
  resource
) when {
  true && (if ((context[""]) has "") then (context has "") else false)
};
