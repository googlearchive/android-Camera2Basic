package com.example.android.camera2basic;

import android.content.Intent;
import android.support.v7.app.AppCompatActivity;
import android.os.Bundle;
import android.view.View;

public class ChooseFrameActivity extends AppCompatActivity {
    public static final String CHOSEN_FRAME = "tokyo.chao.nazoani_camera.FRAME";
    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        setContentView(R.layout.activity_choose_frame);
    }

    public void backToCamera(View view) {
        String chosenFrame = "0";
        switch(view.getId()) {
            case R.id.frame01: {
                chosenFrame = "1";
                break;
            }
            case R.id.frame02: {
                chosenFrame = "2";
                break;
            }
        }
        Intent intent = new Intent(this, CameraActivity.class);
        intent.putExtra(CHOSEN_FRAME, chosenFrame);
        startActivity(intent);
    }
}
