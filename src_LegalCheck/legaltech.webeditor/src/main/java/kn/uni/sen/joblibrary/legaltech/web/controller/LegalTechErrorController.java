package kn.uni.sen.joblibrary.legaltech.web.controller;

import javax.servlet.http.HttpServletRequest;

import org.springframework.boot.web.servlet.error.ErrorController;
import org.springframework.stereotype.Controller;
import org.springframework.ui.Model;
import org.springframework.web.bind.annotation.RequestMapping;

@Controller
public class LegalTechErrorController implements ErrorController
{
	@RequestMapping("/error")
	public String handleError(HttpServletRequest request, Model model)
	{
		Integer statusCode = (Integer) request.getAttribute("javax.servlet.error.status_code");
		Exception exception = (Exception) request.getAttribute("javax.servlet.error.exception");
		String val = org.springframework.http.HttpStatus.
				valueOf(statusCode).name();
		String code = "Status code: <b>" + statusCode + " " + val + "</b>";
		String msg = "";
		if (exception != null)
			msg = exception.getMessage();
		model.addAttribute("errorCode", code);

		model.addAttribute("errorMsg", msg);
		return "error";
	}

	public String getErrorPath()
	{
		return "/error";
	}
}
