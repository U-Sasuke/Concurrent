package com.example.test.concurrent;

import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;
import org.springframework.boot.autoconfigure.jdbc.DataSourceAutoConfiguration;

@SpringBootApplication(exclude= DataSourceAutoConfiguration.class)
public class ConcurrentDemoApplication {

    public static void main(String[] args) {
        SpringApplication.run(ConcurrentDemoApplication.class, args);
    }

}
