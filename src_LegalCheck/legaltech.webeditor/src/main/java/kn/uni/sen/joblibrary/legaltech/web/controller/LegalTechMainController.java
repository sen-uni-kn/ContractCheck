package kn.uni.sen.joblibrary.legaltech.web.controller;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import javax.servlet.http.HttpServletRequest;
import javax.validation.Valid;

import org.springframework.beans.factory.annotation.Value;
import org.springframework.core.io.InputStreamResource;
import org.springframework.core.io.Resource;
import org.springframework.http.MediaType;
import org.springframework.http.ResponseEntity;
import org.springframework.stereotype.Controller;
import org.springframework.ui.Model;
import org.springframework.validation.Errors;
import org.springframework.web.bind.annotation.ModelAttribute;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.multipart.MultipartFile;

import kn.uni.sen.joblibrary.legaltech.common.LegalCheckVersion;
import kn.uni.sen.joblibrary.legaltech.web.run.JobData;
import kn.uni.sen.joblibrary.legaltech.web.run.JobServer_Web;
import kn.uni.sen.joblibrary.legaltech.web.run.JobRun_Web;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;
import kn.uni.sen.jobscheduler.core.model.JobRun;

@Controller
public class LegalTechMainController
{
	// Inject via application.properties
	@Value("${welcome.message}")
	private String welcomeMessage;

	@Value("${error.message}")
	private String errorMessage;

	JobServer_Web server = new JobServer_Web();
	JobRun_Web lastRun = null;

	JobRun_Web getCreateRun(Integer runID, Model model)
	{
		JobRun run = server.createRun(runID);
		model.addAttribute("runID", run.getRunID());
		if (run instanceof JobRun_Web)
			return (JobRun_Web) run;
		return null;
	}

	JobRun_Web getRun(Integer runID)
	{
		JobRun run = server.getRun(runID);
		if (run instanceof JobRun_Web)
			return (JobRun_Web) run;
		return null;
	}

	@RequestMapping(value = { "/", "/index" }, method = RequestMethod.GET)
	public String index(Model model)
	{
		model.addAttribute("message", welcomeMessage);
		return "index";
	}

	@RequestMapping(value = "/newContract", method = RequestMethod.GET)
	public String newEditorHandler(@RequestParam(name = "runID", required = false) Integer runID, Model model)
	{
		lastRun = getCreateRun(runID, model);
		if (lastRun != null)
			runID = lastRun.getRunID();
		return "redirect:/contractEditor?runID=" + runID;
	}

	@RequestMapping(value = "/contractEditor", method = RequestMethod.GET)
	public String editorHandler(@RequestParam(name = "runID", required = false) Integer runID, Model model)
	{
		JobRun_Web run = null;
		if (lastRun != null)
			run = lastRun;
		else
			run = getCreateRun(runID, model);

		if (run == null)
			return "index";
		lastRun = run;
		runID = run.getRunID();

		FormFile form = new FormFile();
		model.addAttribute("FormFile", form);

		model.addAttribute("title", "Vertrag 1");
		model.addAttribute("runID", run.getRunID());
		model.addAttribute("downloadJSON", "/contractEditor/download?runID=" + runID + "&" + "download=json");
		model.addAttribute("downloadText", "/contractEditor/download?runID=" + runID + "&" + "download=txt");
		model.addAttribute("downloadAna", "/contractEditor/download?runID=" + runID + "&" + "download=ana");
		return "contractEditor";
	}

	@RequestMapping(value = "/execution", method = RequestMethod.GET)
	public String executionHandler(@RequestParam(name = "runID", required = false) Integer runID, Model model)
	{
		JobRun_Web run = lastRun;
		// run = getCreateRun(runID, model);
		if (run == null)
			return "index";
		runID = run.getRunID();

		FormFile form = new FormFile();
		model.addAttribute("FormFile", form);

		model.addAttribute("title", "Vertrag 1");
		model.addAttribute("runID", run.getRunID());
		return "diagram";
	}
	
	@RequestMapping(value = "/simulator", method = RequestMethod.GET)
	public String newSimulator(@RequestParam(name = "runID", required = false) Integer runID, Model model)
	{
		JobRun_Web run = null;
		if (lastRun != null)
			run = lastRun;
		else
			run = getCreateRun(runID, model);

		if (run == null)
			return "index";
		lastRun = run;
		runID = run.getRunID();

		FormFile form = new FormFile();
		model.addAttribute("FormFile", form);

		model.addAttribute("title", "Vertrag 1");
		model.addAttribute("runID", run.getRunID());
		return "simulator";
	}
	
	@RequestMapping(path = "/log/analyzeActions", method = RequestMethod.POST)
	public ResponseEntity<?> analyzeActions(@Valid @RequestBody AjaxSetValue data, Model model)
	{
		int runID = data.getsessionID();
		String act = data.getAction();
		AjaxGetContract result = new AjaxGetContract();
		JobRun_Web run = getRun(runID);
		if ((run == null))
			return null;

		run.analyzeActions(null, act);
		return ResponseEntity.ok(result);
	}

	@RequestMapping(value = "/contractEditor", method = RequestMethod.POST)
	public String uploadXMIFilePOST(HttpServletRequest request,
			@RequestParam(name = "runID", required = true) Integer runID,
			@ModelAttribute("UploadForm") FormFile formFile, Model model)
	{
		// System.out.println("uploadXMIFile POST: runID " + runID);
		// System.out.println("uploadXMIFile POST: jobMapID " +
		// runMap.get(runID).getId());
		JobRun_Web run = getRun(runID);
		if ((run == null) || (request == null))
			return "error1";

		String val = request.getParameter("action");
		String fileURL = formFile.getFileName();
		if ((val == null) || (fileURL == null))
			return "error2";

		if (val.contains("Load"))
		{
			String file = loadFile(request, formFile, run);
			run.parseContract(new ResourceFile(file));
		} else if (val.contains("Save"))
		{
			run.saveContract(new ResourceFile(fileURL));
			// todo: send file to user
		}

		// run.addDescription(UploadFormObject.getDescription());
		// this.doUpload(request, UploadFormObject, run);
		return "redirect:/contractEditor?runID=" + runID;
	}

	String loadFile(HttpServletRequest request, FormFile formFile, JobRun_Web run)
	{
		String uploadRootPath = request.getServletContext().getRealPath("upload");
		// System.out.println("uploadRootPath=" + uploadRootPath);

		File uploadRootDir = new File(uploadRootPath);
		// Create directory if it not exists.
		if (!uploadRootDir.exists())
			uploadRootDir.mkdirs();

		String fileName = null;

		MultipartFile[] fileDatas = formFile.getFileDatas();
		for (MultipartFile fileData : fileDatas)
		{
			fileName = fileData.getOriginalFilename();
			if (fileName != null && fileName.length() > 0)
			{
				try
				{
					// Create the file at server
					String filePath = uploadRootDir.getAbsolutePath() + File.separator + fileName;
					File serverFile = new File(filePath);
					BufferedOutputStream stream = new BufferedOutputStream(new FileOutputStream(serverFile));
					stream.write(fileData.getBytes());
					stream.close();
					return filePath;
				} catch (Exception e)
				{
				}
			}
		}
		return null;
	}

	@RequestMapping(path = "/contractEditor/download", method = RequestMethod.GET)
	public ResponseEntity<Resource> download(@RequestParam(name = "runID", required = true) Integer runID,
			@RequestParam(name = "download", required = false) String download, String param)
	{
		JobRun_Web run = getRun(runID);
		if ((run == null))
			return null;

		ResourceFile fileR = null;

		if ("json".equals(download))
		{
			String path = ResourceFolder.appendFolder(run.getFolderText(), "contract.json");
			fileR = new ResourceFile(path);
			run.saveContract(fileR);
		} else if ("txt".equals(download))
		{
			String path = ResourceFolder.appendFolder(run.getFolderText(), "contract.txt");
			fileR = new ResourceFile(path);
			run.saveContractText(fileR);
		}
		if (!!!fileR.exists())
			return null;

		File file = new File(fileR.getData());
		InputStreamResource resource;
		try
		{
			resource = new InputStreamResource(new FileInputStream(file));
		} catch (FileNotFoundException e)
		{
			e.printStackTrace();
			return null;
		}

		return ResponseEntity.ok().contentLength(file.length()).contentType(MediaType.APPLICATION_OCTET_STREAM)
				.body(resource);
	}

	@RequestMapping(path = "/log/analyzeContract", method = RequestMethod.POST)
	public ResponseEntity<?> analyzeContract(@Valid @RequestBody AjaxSetValue data, Model model)
	{
		int runID = data.getsessionID();
		AjaxGetContract result = new AjaxGetContract();
		JobRun_Web run = getRun(runID);
		if ((run == null))
			return null;

		run.analyzeContract(null);
		return ResponseEntity.ok(result);
	}

	@PostMapping("/log/legalContract")
	public ResponseEntity<?> getSearchResultViaAjax2(@Valid @RequestBody Integer runID, Errors errors)
	{
		AjaxGetContract result = new AjaxGetContract();
		// If error, just return a 400 bad request, along with the error message
		if (errors.hasErrors())
		{
			result.setMsg(
					errors.getAllErrors().stream().map(x -> x.getDefaultMessage()).collect(Collectors.joining(",")));
			return ResponseEntity.badRequest().body(result);
		}
		JobRun_Web run = getRun(runID);
		if (run == null)
		{
			result.setMsg("Session not found!");
		} else
		{
			if (!!!run.hasBrick())
			{
				ClassLoader classLoader = getClass().getClassLoader();
				URL fileURL = classLoader.getResource("pattern/vorlage_test.json");
				//assertTrue(fileURL != null);
				run.parseBricks(fileURL);
			}
			result.addContract(run.getContractHtml());
		}
		return ResponseEntity.ok(result);
	}

	@PostMapping("/log/getparas")
	public ResponseEntity<?> getParasViaAjax(@Valid @RequestBody AjaxGetContract result, Errors errors)
	{
		int runID = result.getSessionID();
		// If error, just return a 400 bad request, along with the error message
		if (errors.hasErrors())
		{
			result.setMsg(
					errors.getAllErrors().stream().map(x -> x.getDefaultMessage()).collect(Collectors.joining(",")));
			return ResponseEntity.badRequest().body(result);
		}
		JobRun_Web run = getRun(runID);
		if (run == null)
		{
			result.setMsg("Session not found!");
		} else
		{
			if (!!!run.hasBrick())
			{
				ClassLoader classLoader = getClass().getClassLoader();
				URL fileURL = classLoader.getResource("pattern/vorlage_test.json");
				//assertTrue(fileURL != null);
				run.parseBricks(fileURL);
			}
			result.addContract(run.getParasHtml(result.getVars()));
		}
		return ResponseEntity.ok(result);
	}

	@PostMapping("/log/changeCard")
	public ResponseEntity<?> ajaxChangeCard(@Valid @RequestBody AjaxAddCard data, Model model)
	{
		// Object val = model.getAttribute("cardvalue");
		int runID = data.getsessionID();
		JobRun_Web run = getRun(runID);
		if (run == null)
			return ResponseEntity.ok(null);

		run.changeCard(data.getcardvalue());

		AjaxAddCard result = new AjaxAddCard();
		return ResponseEntity.ok(result);
	}

	@PostMapping("/log/setValue")
	public ResponseEntity<?> ajaxSetValue(@Valid @RequestBody AjaxSetValue data, Model model)
	{
		// Object val = model.getAttribute("cardvalue");
		int runID = data.getsessionID();
		JobRun_Web run = getRun(runID);
		if (run == null)
			return ResponseEntity.ok(null);

		run.setValue(data.getVariable(), data.getValue());

		AjaxAddCard result = new AjaxAddCard();
		return ResponseEntity.ok(result);
	}

	@RequestMapping(value = "/info", method = RequestMethod.GET)
	public String infoHandler(Model model)
	{
		List<JobData> list = new ArrayList<>();

		list.add(new JobData("LegalCheck ", LegalCheckVersion.version));

		model.addAttribute("JobList", list);
		return "info";
	}

	@PostMapping("/log/msg")
	public ResponseEntity<?> getMessageViaAjax(@Valid @RequestBody Integer runID, Errors errors)
	{
		AjaxLog result = new AjaxLog();
		// If error, just return a 400 bad request, along with the error message
		if (errors.hasErrors())
		{
			result.addLog(
					errors.getAllErrors().stream().map(x -> x.getDefaultMessage()).collect(Collectors.joining(",")));
			return ResponseEntity.badRequest().body(result);
		}
		JobRun_Web run = getRun(runID);
		if (run == null)
		{
			result.addLog("Session not found!");
		} else
		{
			JobEvent ev = run.getNextEvent();
			while (ev != null)
			{
				String msg = ev.getText();
				result.addLog(msg);
				ev = run.getNextEvent();
			}
			String res = run.getNextResult();
			while (res != null)
			{
				result.addResult(res);
				res = run.getNextResult();
			}
		}
		return ResponseEntity.ok(result);
	}
}
