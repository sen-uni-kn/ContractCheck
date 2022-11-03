package kn.uni.sen.joblibrary.legaltech.web;

import java.util.concurrent.Executor;
import java.util.concurrent.TimeUnit;

import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;
import org.springframework.http.CacheControl;
import org.springframework.scheduling.annotation.EnableAsync;
import org.springframework.scheduling.concurrent.ThreadPoolTaskExecutor;
import org.springframework.web.servlet.config.annotation.ResourceHandlerRegistry;
import org.springframework.web.servlet.config.annotation.WebMvcConfigurer;

@SpringBootApplication
@Configuration
@EnableAsync
public class LegalTechWebEditor implements WebMvcConfigurer
{
	public static final String version = "1.2.0";

	@Override
	public void addResourceHandlers(ResourceHandlerRegistry registry)
	{
		registry.addResourceHandler("/test/**").addResourceLocations("file:test")
				.setCacheControl(CacheControl.maxAge(2, TimeUnit.HOURS).cachePublic());
		// System.out.println(registry.toString());
	}

	@Bean(name = "threadPoolTaskExecutor")
	public Executor threadPoolTaskExecutor()
	{
		ThreadPoolTaskExecutor executor = new ThreadPoolTaskExecutor();
		executor.setCorePoolSize(8);
		executor.setMaxPoolSize(48);
		executor.setThreadNamePrefix("default_task_executor_thread");
		executor.initialize();
		return executor;
	}

	/*
	 * @Bean public Session_Web createSession() { return new Session_Web(); }
	 */

	public static void main(String[] args)
	{
		// if ("-web".equals(args[0].toLowerCase().replace("--", "-")))
		if (args.length == 0)
		{
			SpringApplication.run(LegalTechWebEditor.class, args);
		} else
			LibraryLegalTech_Console.main(args);
	}
}
