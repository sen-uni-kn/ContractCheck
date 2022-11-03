package kn.uni.sen.joblibrary.legaltech.web.controller;

import java.io.File;
import java.net.URL;
import java.util.LinkedList;
import java.util.List;

import org.springframework.web.multipart.MultipartFile;

import kn.uni.sen.jobscheduler.common.resource.ResourceFile;

public class FormFile
{
	private String description = "";
	private String fileName = "";
	private String analysisName = "";

	// Upload files.
	private MultipartFile[] fileDatas = new MultipartFile[] {};

	// Example files
	private String exampleFile = "";
	private List<String> fileNames = new LinkedList<>();
	private File model;

	public FormFile()
	{
		// System.out.print("here");
	}

	public String getDescription()
	{
		return description;
	}

	public void setDescription(String description)
	{
		this.description = description;
	}

	public String getFileName()
	{
		return fileName;
	}

	public void setFileName(String fileName)
	{
		this.fileName = fileName;
	}

	public MultipartFile[] getFileDatas()
	{
		return fileDatas;
	}

	public void setFileDatas(MultipartFile[] fileDatas)
	{
		this.fileDatas = fileDatas;
		if (fileDatas.length >= 1)
			setFileName(fileDatas[0].getOriginalFilename());
		System.out.println(getFileName());
	}

	public void setAnalysisName(String name)
	{
		analysisName = name;
	}

	public String getAnalysisName()
	{
		return analysisName;
	}

	public List<String> getFileNames()
	{
		return fileNames;
	}

	public String getExampleFile()
	{
		return exampleFile;
	}

	public void setExampleFile(String exampleFile)
	{
		setFileName("");
		this.exampleFile = exampleFile;
	}

	public File getModel(String fileName, String folder)
	{
		if (fileName == null)
			return null;
		// found the model in the modelList
		fileName += ".xmi";
		ClassLoader classLoader = getClass().getClassLoader();
		URL fileURL = classLoader.getResource(fileName);
		if (fileURL == null)
			return null;
		//System.out.println("here13: " + fileURL);
		String file = ResourceFile.writeURL2File(fileURL, folder);
		if (file == null)
			return null;
		//System.out.println("here19" + file);
		model = new File(file);
		return model;
	}

	public void setFileNameList(List<String> fileNameList)
	{
		this.fileNames = fileNameList;
	}
}
